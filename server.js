const express = require('express');
const http = require('http');
const crypto = require('crypto');
const path = require('path');
const { Server } = require('socket.io');

const app = express();
const server = http.createServer(app);
const io = new Server(server);

app.use(express.static(path.join(__dirname, 'public')));

const rooms = new Map();
const MAX_PLAYERS = 5;
const UNO_MAX_PLAYERS = 4;
const MIN_PLAYERS = 2;
const CHAT_MAX_LENGTH = 200;
const CHAT_HISTORY_LIMIT = 50;
const CHAT_COOLDOWN_MS = 600;
const DOBBLE_SYMBOL_COUNT = 57;
const DOBBLE_SYMBOLS_PER_CARD = 8;
const UNO_TURN_MS = 30000;
const UNO_CALL_MS = 3000;
const UNO_DEAL_CARD_STAGGER_MS = 110;
const HALLI_SETTLE_MS = 500;
const HALLI_MIN_VISIBLE_MS = 300;
const HALLI_FRUITS = ['🍓', '🍋', '🍇', '🍈'];
const SEAT_COLORS = new Set(['red', 'blue', 'green', 'orange', 'purple']);
const UNO_COLORS = ['red', 'blue', 'yellow', 'green'];
const INITIAL_SCORE_DECK = [
    { type: 'cat', value: 1, file: 'card_+1' }, { type: 'cat', value: 2, file: 'card_+2' },
    { type: 'cat', value: 3, file: 'card_+3' }, { type: 'cat', value: 4, file: 'card_+4' },
    { type: 'cat', value: 5, file: 'card_+5' }, { type: 'cat', value: 6, file: 'card_+6' },
    { type: 'cat', value: 7, file: 'card_+7' }, { type: 'cat', value: 8, file: 'card_+8' },
    { type: 'cat', value: 9, file: 'card_+9' }, { type: 'cat', value: 10, file: 'card_+10' },
    { type: 'mouse', value: -1, file: 'card_-1' }, { type: 'mouse', value: -2, file: 'card_-2' },
    { type: 'mouse', value: -3, file: 'card_-3' }, { type: 'mouse', value: -4, file: 'card_-4' },
    { type: 'mouse', value: -5, file: 'card_-5' }
];

function newHand() {
    return Array.from({ length: 15 }, (_, index) => index + 1);
}

function normalizeName(value) {
    const cleaned = Array.from(String(value || ''))
        .filter((character) => !/[<>\u0000-\u001f\u007f]/.test(character))
        .join('')
        .trim();
    const maxLength = /[\u1100-\u11ff\u3130-\u318f\uac00-\ud7af]/.test(cleaned) ? 7 : 10;
    const limited = Array.from(cleaned).slice(0, maxLength).join('');
    return limited || '플레이어';
}

function shuffle(array) {
    const shuffled = [...array];
    for (let i = shuffled.length - 1; i > 0; i--) {
        const j = crypto.randomInt(i + 1);
        [shuffled[i], shuffled[j]] = [shuffled[j], shuffled[i]];
    }
    return shuffled;
}

function generateUnoDeck() {
    const cards = [];
    let id = 1;
    const add = (color, kind, value) => cards.push({ id: id++, color, kind, value });

    for (const color of UNO_COLORS) {
        add(color, 'number', 0);
        for (let value = 1; value <= 9; value++) {
            add(color, 'number', value);
            add(color, 'number', value);
        }
        for (const kind of ['skip', 'reverse', 'draw2']) {
            add(color, kind, kind);
            add(color, kind, kind);
        }
    }
    for (let i = 0; i < 4; i++) {
        add(null, 'wild', 'wild');
        add(null, 'wild4', 'wild4');
    }
    return cards;
}

function generateHalliDeck() {
    const cards = [];
    let id = 1;
    // 공식 분포: 과일마다 1개 5장, 2개 3장, 3개 3장, 4개 2장, 5개 1장.
    const counts = [[1, 5], [2, 3], [3, 3], [4, 2], [5, 1]];
    for (let fruit = 0; fruit < HALLI_FRUITS.length; fruit++) {
        for (const [amount, copies] of counts) {
            for (let copy = 0; copy < copies; copy++) {
                cards.push({ id: id++, fruit, amount });
            }
        }
    }
    return cards;
}

function clearHalliTimer(room) {
    if (room?.halli?.settleTimer) clearTimeout(room.halli.settleTimer);
    if (room?.halli) room.halli.settleTimer = null;
}

function halliFaceUpTotal(room) {
    return Object.values(room.players).reduce((sum, player) => sum + (player.halliFaceUp?.length || 0), 0);
}

function halliHasCards(player) {
    return (player.halliDraw?.length || 0) + (player.halliFaceUp?.length || 0) > 0;
}

function halliFinishIfNeeded(room) {
    const standing = Object.values(room.players).filter(halliHasCards);
    if (standing.length <= 1) {
        room.halli.winnerId = standing[0]?.id || null;
        room.gameState = 'GAME_OVER';
        clearHalliTimer(room);
        return true;
    }
    if (standing.every((player) => !player.halliDraw.length) && !halliIsExactFive(room)) {
        const winner = standing.sort((a, b) =>
            ((b.halliDraw?.length || 0) + (b.halliFaceUp?.length || 0)) -
            ((a.halliDraw?.length || 0) + (a.halliFaceUp?.length || 0))
        )[0];
        room.halli.winnerId = winner?.id || null;
        room.gameState = 'GAME_OVER';
        clearHalliTimer(room);
        return true;
    }
    return false;
}

function halliNextTurn(room, fromIndex = room.halli.currentIndex) {
    const order = room.halli.playerOrder;
    for (let offset = 1; offset <= order.length; offset++) {
        const index = (fromIndex + offset) % order.length;
        const player = room.players[order[index]];
        if (player?.halliDraw?.length) {
            room.halli.currentIndex = index;
            return;
        }
    }
    room.halli.currentIndex = fromIndex;
}

function halliIsExactFive(room) {
    const totals = [0, 0, 0, 0];
    for (const player of Object.values(room.players)) {
        const card = player.halliFaceUp?.[player.halliFaceUp.length - 1];
        if (card) totals[card.fruit] += card.amount;
    }
    return totals.some((total) => total === 5);
}

function halliResolveClaims(room) {
    const halli = room.halli;
    if (!halli || room.gameState !== 'HALLI_SETTLING') return;
    clearHalliTimer(room);
    const winnerClaim = [...halli.claims].sort((a, b) => a.elapsedMs - b.elapsedMs || a.receivedAt - b.receivedAt)[0];
    if (!winnerClaim) {
        room.gameState = 'HALLI_PLAYING';
        broadcastRoom(room);
        return;
    }
    const winner = room.players[winnerClaim.playerId];
    const winnings = [];
    for (const playerId of halli.playerOrder) {
        const player = room.players[playerId];
        if (player?.halliFaceUp?.length) winnings.push(...player.halliFaceUp.splice(0));
    }
    if (winner && winnings.length) {
        // 획득 카드는 자기 덱 맨 아래에 들어간다. pop()으로 뽑으므로 배열 앞에 붙인다.
        winner.halliDraw.unshift(...winnings);
        halli.lastResult = {
            id: ++halli.resultSequence,
            type: 'correct',
            winnerId: winner.id,
            cardCount: winnings.length,
            reactionTimes: { ...halli.reactionTimes }
        };
        winner.score = winner.halliDraw.length;
    }
    halli.reactionTimes = {};
    halli.claims = [];
    halli.ringedPlayers = {};
    halli.boardVersion++;
    halliNextTurn(room, halli.currentIndex);
    room.gameState = 'HALLI_PLAYING';
    halliFinishIfNeeded(room);
    broadcastRoom(room);
}

function halliGivePenalty(room, offender) {
    const halli = room.halli;
    const recipients = halli.playerOrder.map((id) => room.players[id])
        .filter((player) => player && player.id !== offender.id);
    let paid = 0;
    for (const recipient of recipients) {
        let card = offender.halliDraw.pop();
        if (!card) card = offender.halliFaceUp.pop();
        if (!card) break;
        recipient.halliDraw.unshift(card);
        recipient.score = recipient.halliDraw.length;
        paid++;
    }
    offender.score = offender.halliDraw.length;
    halli.lastResult = {
        id: ++halli.resultSequence,
        type: 'wrong',
        offenderId: offender.id,
        penaltyCount: paid,
        reactionTimes: { ...halli.reactionTimes }
    };
    halliFinishIfNeeded(room);
}

function unoCardPoints(card) {
    return card.kind === 'number' ? Number(card.value) || 0 : 10;
}

function unoHandPoints(hand) {
    return hand.reduce((sum, card) => sum + unoCardPoints(card), 0);
}

function clearUnoTimer(room) {
    if (room?.uno?.timer) clearTimeout(room.uno.timer);
    if (room?.uno?.dealTimer) clearTimeout(room.uno.dealTimer);
    if (room?.uno) room.uno.timer = null;
    if (room?.uno) room.uno.dealTimer = null;
}

function scheduleUnoDeal(room) {
    if (!room?.uno || room.gameState !== 'UNO_DEALING') return;
    if (room.uno.dealTimer) clearTimeout(room.uno.dealTimer);
    room.uno.dealTimer = setTimeout(() => {
        if (room.gameState !== 'UNO_DEALING' || !room.uno) return;
        room.uno.dealTimer = null;
        room.gameState = 'UNO_PLAYING';
        room.uno.turnExpiresAt = Date.now() + UNO_TURN_MS;
        scheduleUnoTimer(room);
        broadcastRoom(room);
    }, Math.max(0, room.uno.dealEndsAt - Date.now()));
}

function unoPlayerAt(room, offset) {
    const uno = room.uno;
    const count = uno.playerOrder.length;
    if (!count) return null;
    const index = (uno.currentIndex + uno.direction * offset % count + count) % count;
    return room.players[uno.playerOrder[index]] || null;
}

function isUnoCardPlayable(card, uno) {
    const top = uno.discardPile[uno.discardPile.length - 1];
    return card.kind === 'wild' || card.kind === 'wild4' ||
        card.color === uno.currentColor ||
        (card.kind === top.kind && card.value === top.value);
}

function drawUnoCard(room) {
    const uno = room.uno;
    if (!uno.drawPile.length && uno.discardPile.length > 1) {
        const topCard = uno.discardPile.pop();
        uno.drawPile = shuffle(uno.discardPile);
        uno.discardPile = [topCard];
    }
    return uno.drawPile.pop() || null;
}

function drawUnoCards(room, player, count) {
    const drawn = [];
    for (let i = 0; i < count; i++) {
        const card = drawUnoCard(room);
        if (!card) break;
        player.hand.push(card);
        drawn.push(card);
    }
    return drawn;
}

function nextUnoTurn(room, steps = 1) {
    const uno = room.uno;
    clearUnoTimer(room);
    uno.pendingUnoCall = null;
    uno.drewCardId = null;
    const count = uno.playerOrder.length;
    if (!count) return;
    uno.currentIndex = (uno.currentIndex + uno.direction * steps % count + count) % count;
    uno.turnExpiresAt = Date.now() + UNO_TURN_MS;
    scheduleUnoTimer(room);
}

function scheduleUnoTimer(room) {
    clearUnoTimer(room);
    const uno = room.uno;
    if (!uno || room.gameState !== 'UNO_PLAYING') return;
    const deadline = uno.pendingUnoCall?.deadline || uno.turnExpiresAt;
    uno.timer = setTimeout(() => {
        if (room.gameState !== 'UNO_PLAYING' || !room.uno) return;
        const current = room.players[room.uno.playerOrder[room.uno.currentIndex]];
        if (!current) return;

        if (room.uno.pendingUnoCall) {
            const pending = room.uno.pendingUnoCall;
            if (current.id !== pending.playerId) return;
            const drawn = drawUnoCards(room, current, 2);
            room.uno.lastAction = {
                id: ++room.uno.actionSequence, type: 'uno-missed', playerId: current.id,
                drawCount: drawn.length
            };
            nextUnoTurn(room, pending.nextSteps);
        } else {
            let drawn = [];
            if (room.uno.drewCardId === null) drawn = drawUnoCards(room, current, 1);
            room.uno.lastAction = {
                id: ++room.uno.actionSequence, type: 'timeout', playerId: current.id,
                drawCount: drawn.length
            };
            nextUnoTurn(room, 1);
        }
        broadcastRoom(room);
    }, Math.max(0, deadline - Date.now()));
}

function generateDobbleDeck() {
    // Projective plane of order 7: 57 cards, 8 symbols per card,
    // and exactly one shared symbol between every pair of cards.
    const cards = [];
    const point = (x, y) => (y * 7) + x;

    for (let slope = 0; slope < 7; slope++) {
        for (let intercept = 0; intercept < 7; intercept++) {
            const symbols = [];
            for (let x = 0; x < 7; x++) {
                symbols.push(point(x, (slope * x + intercept) % 7));
            }
            symbols.push(49 + slope);
            cards.push({ id: cards.length, symbols });
        }
    }

    for (let x = 0; x < 7; x++) {
        const symbols = [];
        for (let y = 0; y < 7; y++) symbols.push(point(x, y));
        symbols.push(56);
        cards.push({ id: cards.length, symbols });
    }

    cards.push({ id: cards.length, symbols: Array.from({ length: 8 }, (_, i) => 49 + i) });
    return cards;
}

function generateRoomCode() {
    if (rooms.size >= 9000) {
        throw new Error('생성 가능한 방 번호가 모두 사용 중입니다.');
    }
    let code;
    do {
        code = String(crypto.randomInt(1000, 10000));
    } while (rooms.has(code));
    return code;
}

// 클라이언트에는 본인 손패만 전달하고, 선택한 카드는 라운드 결과 전까지 숨깁니다.
function snapshotFor(room, viewerId) {
    const revealCards = room.gameState === 'ROUND_RESULT' || room.gameState === 'GAME_OVER';
    const players = {};

    for (const player of Object.values(room.players)) {
        const isViewer = player.id === viewerId;
        players[player.id] = {
            id: player.id,
            name: player.name,
            color: player.color,
            ready: player.ready,
            score: player.score,
            hand: isViewer || (room.gameMode === 'UNO' && room.gameState === 'GAME_OVER') ? [...player.hand] : [],
            unoHandCount: room.gameMode === 'UNO' ? player.hand.length : 0,
            unoHandPoints: room.gameMode === 'UNO' && room.gameState === 'GAME_OVER' ? unoHandPoints(player.hand) : null,
            playedCard: isViewer || revealCards
                ? player.playedCard
                : (player.playedCard === null ? null : 'HIDDEN'),
            wonCards: player.wonCards.map((card) => ({ ...card })),
            dobbleActiveCard: isViewer && player.dobbleStack?.length
                ? { ...player.dobbleStack[player.dobbleStack.length - 1], symbols: [...player.dobbleStack[player.dobbleStack.length - 1].symbols] }
                : null,
            dobbleCardCount: player.dobbleStack?.length || 0,
            dobbleLockMs: isViewer ? Math.max(0, (player.dobbleLockedUntil || 0) - Date.now()) : 0,
            dobbleLockVersion: isViewer ? (player.dobbleLockVersion ?? null) : null,
            halliDrawCount: player.halliDraw?.length || 0,
            halliFaceUp: player.halliFaceUp?.length ? { ...player.halliFaceUp[player.halliFaceUp.length - 1] } : null,
            halliFaceUpCount: player.halliFaceUp?.length || 0,
            halliEliminated: room.gameMode === 'HALLI' && !halliHasCards(player)
        };
    }

    return {
        serverTime: Date.now(),
        roomCode: room.roomCode,
        hostId: room.hostId,
        gameMode: room.gameMode || 'EYE',
        players,
        gameState: room.gameState,
        currentRound: room.currentRound,
        scoreDeck: [],
        tableScoreCards: room.tableScoreCards.map((card) => ({ ...card })),
        lastWinnerId: room.lastWinnerId,
        roundResults: room.roundResults.map((result) => ({ ...result })),
        dobbleCenterCard: room.dobbleCenterCard
            ? { ...room.dobbleCenterCard, symbols: [...room.dobbleCenterCard.symbols] }
            : null,
        dobbleDeckCount: (room.dobbleDeck?.length || 0) + (room.dobbleCenterCard ? 1 : 0),
        dobbleCardVersion: room.dobbleCardVersion || 0,
        lastDobbleClaim: room.lastDobbleClaim ? {
            id: room.lastDobbleClaim.id,
            winnerId: room.lastDobbleClaim.winnerId,
            card: { ...room.lastDobbleClaim.card, symbols: [...room.lastDobbleClaim.card.symbols] }
        } : null,
        halli: room.halli ? {
            playerOrder: [...room.halli.playerOrder],
            currentPlayerId: room.halli.playerOrder[room.halli.currentIndex] || null,
            boardVersion: room.halli.boardVersion,
            deckCount: room.halli.deckCount,
            settling: room.gameState === 'HALLI_SETTLING',
            exactFive: halliIsExactFive(room),
            reactionTimes: { ...room.halli.reactionTimes },
            lastResult: room.halli.lastResult ? {
                ...room.halli.lastResult,
                reactionTimes: { ...room.halli.lastResult.reactionTimes }
            } : null,
            winnerId: room.halli.winnerId
        } : null,
        uno: room.uno ? {
            playerOrder: [...room.uno.playerOrder],
            currentPlayerId: room.uno.playerOrder[room.uno.currentIndex] || null,
            direction: room.uno.direction,
            currentColor: room.uno.currentColor,
            topCard: room.uno.discardPile.length ? { ...room.uno.discardPile[room.uno.discardPile.length - 1] } : null,
            discardCount: room.uno.discardPile.length,
            drawPileCount: room.uno.drawPile.length,
            turnExpiresAt: room.uno.turnExpiresAt,
            dealId: room.uno.dealId,
            dealEndsAt: room.uno.dealEndsAt,
            pendingUnoCall: room.uno.pendingUnoCall ? {
                playerId: room.uno.pendingUnoCall.playerId,
                deadline: room.uno.pendingUnoCall.deadline
            } : null,
            drewCardId: room.uno.playerOrder[room.uno.currentIndex] === viewerId ? room.uno.drewCardId : null,
            lastAction: room.uno.lastAction ? {
                ...room.uno.lastAction,
                card: room.uno.lastAction.card ? { ...room.uno.lastAction.card } : null
            } : null,
            winnerId: room.uno.winnerId,
            winnerPoints: room.uno.winnerPoints || 0
        } : null
    };
}

function broadcastRoom(room) {
    for (const playerId of Object.keys(room.players)) {
        const clientSocket = io.sockets.sockets.get(playerId);
        if (clientSocket) {
            clientSocket.emit('update-room', snapshotFor(room, playerId));
        }
    }
}

io.on('connection', (socket) => {
    let currentRoomCode = null;

    function getCurrentRoom() {
        return currentRoomCode ? rooms.get(currentRoomCode) : null;
    }

    function rejectIfAlreadyInRoom() {
        const currentRoom = getCurrentRoom();
        if (currentRoom && currentRoom.players[socket.id]) {
            socket.emit('error-msg', '이미 방에 들어와 있어! 새로고침 후 다시 입장해줘.');
            return true;
        }
        currentRoomCode = null;
        return false;
    }

    function joinRoomLogic(room, name) {
        currentRoomCode = room.roomCode;
        socket.join(room.roomCode);
        if (!room.hostId) room.hostId = socket.id;

        room.players[socket.id] = {
            id: socket.id,
            name: normalizeName(name),
            color: null,
            ready: false,
            score: 0,
            hand: [],
            playedCard: null,
            wonCards: [],
            dobbleStack: [],
            dobbleLockedUntil: 0,
            dobbleLockVersion: 0,
            halliDraw: [],
            halliFaceUp: []
        };
        broadcastRoom(room);
        socket.emit('chat-history', room.chatMessages || []);
    }

    function requireHost(room) {
        if (room.hostId !== socket.id) {
            socket.emit('error-msg', '이 기능은 방장만 사용할 수 있어!');
            return false;
        }
        return true;
    }

    socket.on('create-room', (payload) => {
        if (rejectIfAlreadyInRoom()) return;

        const createData = typeof payload === 'string' ? { name: payload, gameMode: 'EYE' } : (payload || {});
        const gameMode = ['DOBBLE', 'UNO', 'HALLI'].includes(createData.gameMode) ? createData.gameMode : 'EYE';
        let roomCode;
        try {
            roomCode = generateRoomCode();
        } catch (error) {
            socket.emit('error-msg', error.message);
            return;
        }

        const room = {
            roomCode,
            hostId: socket.id,
            gameMode,
            players: {},
            gameState: 'LOBBY',
            currentRound: 0,
            scoreDeck: [],
            tableScoreCards: [],
            lastWinnerId: null,
            roundResults: [],
            roundToken: 0,
            chatMessages: [],
            dobbleDeck: [],
            dobbleCenterCard: null,
            dobbleCardVersion: 0,
            lastDobbleClaim: null,
            uno: null,
            halli: null
        };
        rooms.set(roomCode, room);
        joinRoomLogic(room, createData.name);
    });

    socket.on('join-room', (payload = {}) => {
        if (rejectIfAlreadyInRoom()) return;

        const cleanCode = String(payload.roomCode || '').trim();
        const room = rooms.get(cleanCode);

        if (!/^\d{4}$/.test(cleanCode) || !room) {
            socket.emit('error-msg', '존재하지 않는 방 번호야! 다시 확인해줘.');
            return;
        }
        if (room.gameState !== 'LOBBY') {
            socket.emit('error-msg', '이미 게임이 시작된 방이라 들어갈 수 없어!');
            return;
        }
        const roomPlayerLimit = room.gameMode === 'UNO' ? UNO_MAX_PLAYERS : MAX_PLAYERS;
        if (Object.keys(room.players).length >= roomPlayerLimit) {
            socket.emit('error-msg', room.gameMode === 'UNO'
                ? '냥이 UNO는 최대 4명까지 함께할 수 있어!'
                : '방 인원(최대 5명)이 꽉 찼어!');
            return;
        }

        joinRoomLogic(room, payload.name);
    });

    socket.on('select-seat', (color) => {
        const room = getCurrentRoom();
        if (!room || room.gameState !== 'LOBBY') return;

        const player = room.players[socket.id];
        if (!player || player.ready) return;
        if (!SEAT_COLORS.has(color)) {
            socket.emit('error-msg', '선택할 수 없는 자리야!');
            return;
        }

        const isTaken = Object.values(room.players).some(
            (other) => other.id !== socket.id && other.color === color
        );
        if (isTaken) {
            socket.emit('error-msg', '이미 다른 친구가 앉은 자리야!');
            return;
        }

        player.color = color;
        broadcastRoom(room);
    });

    socket.on('toggle-ready', () => {
        const room = getCurrentRoom();
        if (!room || room.gameState !== 'LOBBY') return;

        const player = room.players[socket.id];
        if (player && player.color !== null) {
            player.ready = !player.ready;
            broadcastRoom(room);
        }
    });

    socket.on('chat-message', (payload = {}) => {
        const room = getCurrentRoom();
        const player = room && room.players[socket.id];
        if (!room || !player) return;

        const rawText = typeof payload?.text === 'string' ? payload.text : '';
        const text = Array.from(rawText.replace(/[\u0000-\u001f\u007f]/g, ''))
            .slice(0, CHAT_MAX_LENGTH)
            .join('')
            .trim();
        if (!text) return;

        const now = Date.now();
        if (now - (socket.data.lastChatAt || 0) < CHAT_COOLDOWN_MS) return;
        socket.data.lastChatAt = now;

        const message = {
            name: player.name,
            text,
            createdAt: new Date(now).toISOString()
        };
        room.chatMessages.push(message);
        if (room.chatMessages.length > CHAT_HISTORY_LIMIT) {
            room.chatMessages.shift();
        }

        io.to(room.roomCode).emit('chat-message', message);
    });

    socket.on('start-game', () => {
        const room = getCurrentRoom();
        if (!room || room.gameState !== 'LOBBY' || !requireHost(room)) return;

        const allPlayers = Object.values(room.players);
        const seatedPlayers = allPlayers.filter((player) => player.color !== null);

        if (seatedPlayers.length < MIN_PLAYERS) {
            socket.emit('error-msg', '게임을 시작하려면 최소 2명이 자리에 앉아야 해!');
            return;
        }
        if (room.gameMode === 'UNO' && seatedPlayers.length > UNO_MAX_PLAYERS) {
            socket.emit('error-msg', '냥이 UNO는 최대 4명까지 할 수 있어!');
            return;
        }
        if (seatedPlayers.length !== allPlayers.length || seatedPlayers.some((player) => !player.ready)) {
            socket.emit('error-msg', '모든 플레이어가 자리에 앉고 준비 완료해야 시작할 수 있어!');
            return;
        }

        room.roundToken += 1;
        room.lastWinnerId = null;
        room.roundResults = [];
        room.scoreDeck = [];
        room.tableScoreCards = [];
        room.dobbleDeck = [];
        room.dobbleCenterCard = null;
        room.dobbleCardVersion = 0;
        room.lastDobbleClaim = null;
        clearUnoTimer(room);
        room.uno = null;
        clearHalliTimer(room);
        room.halli = null;

        seatedPlayers.forEach((player) => {
            player.score = 0;
            player.hand = [];
            player.playedCard = null;
            player.wonCards = [];
            player.dobbleStack = [];
            player.dobbleLockedUntil = 0;
            player.dobbleLockVersion = 0;
            player.halliDraw = [];
            player.halliFaceUp = [];
        });

        if (room.gameMode === 'DOBBLE') {
            const deck = shuffle(generateDobbleDeck());
            seatedPlayers.forEach((player) => {
                player.dobbleStack = [deck.pop()];
                player.score = 1;
            });
            room.dobbleDeck = deck;
            room.dobbleCenterCard = room.dobbleDeck.pop();
            room.dobbleCardVersion = 1;
            room.currentRound = 0;
            room.gameState = 'DOBBLE_PLAYING';
        } else if (room.gameMode === 'UNO') {
            const drawPile = shuffle(generateUnoDeck());
            for (let dealt = 0; dealt < 7; dealt++) {
                for (const player of seatedPlayers) player.hand.push(drawPile.pop());
            }
            const firstNumberIndex = drawPile.findIndex((card) => card.kind === 'number');
            const firstCard = drawPile.splice(firstNumberIndex, 1)[0];
            room.uno = {
                drawPile,
                discardPile: [firstCard],
                playerOrder: seatedPlayers.map((player) => player.id),
                currentIndex: 0,
                direction: 1,
                currentColor: firstCard.color,
                turnExpiresAt: 0,
                dealId: room.roundToken,
                dealEndsAt: Date.now() + Math.max(0, (seatedPlayers.length * 7 - 1) * UNO_DEAL_CARD_STAGGER_MS + 700),
                pendingUnoCall: null,
                drewCardId: null,
                actionSequence: 0,
                lastAction: null,
                winnerId: null,
                winnerPoints: 0,
                timer: null,
                dealTimer: null
            };
            room.currentRound = 1;
            room.gameState = 'UNO_DEALING';
            scheduleUnoDeal(room);
        } else if (room.gameMode === 'HALLI') {
            const deck = shuffle(generateHalliDeck());
            for (let index = 0; index < deck.length; index++) {
                seatedPlayers[index % seatedPlayers.length].halliDraw.push(deck[index]);
            }
            seatedPlayers.forEach((player) => { player.score = player.halliDraw.length; });
            room.halli = {
                playerOrder: seatedPlayers.map((player) => player.id),
                currentIndex: 0,
                boardVersion: 1,
                deckCount: deck.length,
                flipAllowedAt: 0,
                reactionTimes: {},
                ringedPlayers: {},
                claims: [],
                lastResult: null,
                resultSequence: 0,
                winnerId: null,
                settleTimer: null
            };
            room.currentRound = 1;
            room.gameState = 'HALLI_PLAYING';
        } else {
            room.gameState = 'PLAYING';
            room.currentRound = 1;
            room.scoreDeck = shuffle(INITIAL_SCORE_DECK);
            room.tableScoreCards = [room.scoreDeck.pop()];
            seatedPlayers.forEach((player) => {
                player.hand = newHand();
            });
        }

        broadcastRoom(room);
    });

    socket.on('reset-game', () => {
        const room = getCurrentRoom();
        if (!room || !requireHost(room)) return;

        room.roundToken += 1;
        clearUnoTimer(room);
        room.uno = null;
        room.gameState = 'LOBBY';
        room.currentRound = 0;
        room.scoreDeck = [];
        room.tableScoreCards = [];
        room.lastWinnerId = null;
        room.roundResults = [];
        room.dobbleDeck = [];
        room.dobbleCenterCard = null;
        room.dobbleCardVersion = 0;
        room.lastDobbleClaim = null;
        clearHalliTimer(room);
        room.halli = null;

        Object.values(room.players).forEach((player) => {
            player.ready = false;
            player.score = 0;
            player.hand = [];
            player.playedCard = null;
            player.wonCards = [];
            player.dobbleStack = [];
            player.dobbleLockedUntil = 0;
            player.dobbleLockVersion = 0;
            player.halliDraw = [];
            player.halliFaceUp = [];
        });

        broadcastRoom(room);
    });

    socket.on('halli-flip', (payload = {}) => {
        const room = getCurrentRoom();
        const halli = room?.halli;
        const player = room?.players[socket.id];
        if (!room || room.gameMode !== 'HALLI' || room.gameState !== 'HALLI_PLAYING' || !halli || !player) return;
        if (halli.playerOrder[halli.currentIndex] !== socket.id || !player.halliDraw.length) return;
        const now = Date.now();
        if (now < halli.flipAllowedAt) return;
        const card = player.halliDraw.pop();
        player.halliFaceUp.push(card);
        player.score = player.halliDraw.length;
        halli.boardVersion++;
        halli.reactionTimes = {};
        halli.claims = [];
        halli.ringedPlayers = {};
        halli.flipAllowedAt = now + HALLI_MIN_VISIBLE_MS;
        halli.lastResult = null;
        const oldIndex = halli.currentIndex;
        halliNextTurn(room, oldIndex);
        room.currentRound++;
        halliFinishIfNeeded(room);
        broadcastRoom(room);
    });

    socket.on('halli-ring', (payload = {}) => {
        const room = getCurrentRoom();
        const halli = room?.halli;
        const player = room?.players[socket.id];
        if (!room || room.gameMode !== 'HALLI' || !halli || !player || !halliHasCards(player)) return;
        if (!['HALLI_PLAYING', 'HALLI_SETTLING'].includes(room.gameState)) return;
        const version = Number(payload.boardVersion);
        if (!Number.isInteger(version) || version !== halli.boardVersion) return;
        if (Object.prototype.hasOwnProperty.call(halli.ringedPlayers, socket.id)) return;
        const reported = Number(payload.elapsedMs);
        const elapsedMs = Number.isFinite(reported) ? Math.max(0, Math.min(10000, Math.round(reported))) : 10000;
        halli.ringedPlayers[socket.id] = true;
        halli.reactionTimes[socket.id] = elapsedMs;

        if (!halliIsExactFive(room)) {
            halliGivePenalty(room, player);
        } else {
            halli.claims.push({ playerId: player.id, elapsedMs, receivedAt: Date.now() });
            if (room.gameState !== 'HALLI_SETTLING') {
                room.gameState = 'HALLI_SETTLING';
                halli.settleTimer = setTimeout(() => halliResolveClaims(room), HALLI_SETTLE_MS);
            }
        }
        broadcastRoom(room);
    });

    socket.on('uno-draw', () => {
        const room = getCurrentRoom();
        const uno = room?.uno;
        if (!room || room.gameMode !== 'UNO' || room.gameState !== 'UNO_PLAYING' || !uno) return;
        const player = room.players[socket.id];
        if (!player || uno.playerOrder[uno.currentIndex] !== socket.id || uno.pendingUnoCall || uno.drewCardId !== null) return;
        if (Date.now() >= uno.turnExpiresAt) return;

        const card = drawUnoCard(room);
        if (!card) {
            uno.lastAction = { id: ++uno.actionSequence, type: 'draw-empty', playerId: player.id };
            nextUnoTurn(room, 1);
        } else {
            player.hand.push(card);
            uno.lastAction = { id: ++uno.actionSequence, type: 'draw', playerId: player.id };
            if (isUnoCardPlayable(card, uno)) {
                uno.drewCardId = card.id;
                scheduleUnoTimer(room);
            } else {
                nextUnoTurn(room, 1);
            }
        }
        broadcastRoom(room);
    });

    socket.on('uno-end-turn', () => {
        const room = getCurrentRoom();
        const uno = room?.uno;
        if (!room || room.gameMode !== 'UNO' || room.gameState !== 'UNO_PLAYING' || !uno) return;
        if (uno.playerOrder[uno.currentIndex] !== socket.id || uno.pendingUnoCall || uno.drewCardId === null) return;
        uno.lastAction = { id: ++uno.actionSequence, type: 'pass', playerId: socket.id };
        nextUnoTurn(room, 1);
        broadcastRoom(room);
    });

    socket.on('uno-play-card', (payload = {}) => {
        const room = getCurrentRoom();
        const uno = room?.uno;
        const player = room?.players[socket.id];
        if (!room || room.gameMode !== 'UNO' || room.gameState !== 'UNO_PLAYING' || !uno || !player) return;
        if (uno.playerOrder[uno.currentIndex] !== socket.id || uno.pendingUnoCall) return;
        if (Date.now() >= uno.turnExpiresAt) return;

        const cardId = Number(payload.cardId);
        const handIndex = player.hand.findIndex((card) => card.id === cardId);
        if (!Number.isInteger(cardId) || handIndex < 0) return;
        const card = player.hand[handIndex];
        if (uno.drewCardId !== null && card.id !== uno.drewCardId) return;
        if (!isUnoCardPlayable(card, uno)) return;

        const chosenColor = UNO_COLORS.includes(payload.chosenColor) ? payload.chosenColor : null;
        if ((card.kind === 'wild' || card.kind === 'wild4') && !chosenColor) {
            socket.emit('error-msg', '카드 색을 먼저 골라줘!');
            return;
        }
        if (card.kind === 'wild4' && player.hand.some((held) => held.id !== card.id && held.color === uno.currentColor)) {
            socket.emit('error-msg', '같은 색 카드가 있으면 +4 카드는 낼 수 없어!');
            return;
        }

        player.hand.splice(handIndex, 1);
        uno.discardPile.push({ ...card });
        uno.currentColor = chosenColor || card.color;
        uno.drewCardId = null;

        let nextSteps = 1;
        let effectTargetId = null;
        let effectDrawCount = 0;
        if (card.kind === 'reverse') {
            uno.direction *= -1;
            if (uno.playerOrder.length === 2) nextSteps = 2;
        } else if (card.kind === 'skip') {
            nextSteps = 2;
        } else if (card.kind === 'draw2' || card.kind === 'wild4') {
            const target = unoPlayerAt(room, 1);
            if (target) {
                effectTargetId = target.id;
                effectDrawCount = drawUnoCards(room, target, card.kind === 'draw2' ? 2 : 4).length;
            }
            nextSteps = 2;
        }

        uno.lastAction = {
            id: ++uno.actionSequence, type: 'play', playerId: player.id,
            card: { ...card, chosenColor: chosenColor || null },
            effectTargetId, effectDrawCount
        };

        if (player.hand.length === 0) {
            clearUnoTimer(room);
            uno.pendingUnoCall = null;
            uno.winnerId = player.id;
            uno.winnerPoints = 0;
            player.score = 0;
            room.gameState = 'GAME_OVER';
        } else if (player.hand.length === 1) {
            clearUnoTimer(room);
            uno.pendingUnoCall = {
                playerId: player.id,
                deadline: Date.now() + UNO_CALL_MS,
                nextSteps
            };
            scheduleUnoTimer(room);
        } else {
            nextUnoTurn(room, nextSteps);
        }
        broadcastRoom(room);
    });

    socket.on('uno-call', () => {
        const room = getCurrentRoom();
        const uno = room?.uno;
        const pending = uno?.pendingUnoCall;
        if (!room || room.gameMode !== 'UNO' || room.gameState !== 'UNO_PLAYING' || !uno || !pending) return;
        if (pending.playerId !== socket.id || Date.now() > pending.deadline) return;
        const nextSteps = pending.nextSteps;
        uno.lastAction = { id: ++uno.actionSequence, type: 'uno-call', playerId: socket.id };
        nextUnoTurn(room, nextSteps);
        broadcastRoom(room);
    });

    socket.on('dobble-answer', (payload = {}) => {
        const room = getCurrentRoom();
        if (!room || room.gameMode !== 'DOBBLE' || room.gameState !== 'DOBBLE_PLAYING') return;

        const player = room.players[socket.id];
        if (!player || player.color === null || !player.dobbleStack?.length) return;

        const version = Number(payload?.cardVersion);
        if (!Number.isInteger(version) || version !== room.dobbleCardVersion) return;

        const now = Date.now();
        if (player.dobbleLockedUntil > now && player.dobbleLockVersion === room.dobbleCardVersion) return;

        const symbolId = Number(payload?.symbolId);
        const ownCard = player.dobbleStack[player.dobbleStack.length - 1];
        const isCorrect = Number.isInteger(symbolId) &&
            symbolId >= 0 && symbolId < DOBBLE_SYMBOL_COUNT &&
            ownCard.symbols.includes(symbolId) &&
            room.dobbleCenterCard.symbols.includes(symbolId);

        if (!isCorrect) {
            player.dobbleLockedUntil = now + 3000;
            player.dobbleLockVersion = room.dobbleCardVersion;
            broadcastRoom(room);
            return;
        }

        const claimedCard = room.dobbleCenterCard;
        player.dobbleStack.push(claimedCard);
        player.score = player.dobbleStack.length;
        room.dobbleCenterCard = room.dobbleDeck.pop() || null;
        room.dobbleCardVersion += 1;
        room.lastDobbleClaim = {
            id: room.dobbleCardVersion,
            winnerId: player.id,
            card: claimedCard
        };

        for (const other of Object.values(room.players)) {
            other.dobbleLockedUntil = 0;
            other.dobbleLockVersion = room.dobbleCardVersion;
        }

        if (!room.dobbleCenterCard) {
            room.gameState = 'GAME_OVER';
        }
        broadcastRoom(room);
    });

    socket.on('play-card', (cardValue) => {
        const room = getCurrentRoom();
        if (!room || room.gameState !== 'PLAYING') return;

        const player = room.players[socket.id];
        if (!player || player.color === null) return;
        if (player.playedCard !== null) {
            socket.emit('error-msg', '이번 라운드에 이미 카드를 냈어!');
            return;
        }
        if (!Number.isInteger(cardValue) || !player.hand.includes(cardValue)) {
            socket.emit('error-msg', '낼 수 없는 숫자 카드야!');
            return;
        }

        player.hand.splice(player.hand.indexOf(cardValue), 1);
        player.playedCard = cardValue;
        broadcastRoom(room);

        const activePlayers = Object.values(room.players).filter((entry) => entry.color !== null);
        if (activePlayers.length >= MIN_PLAYERS && activePlayers.every((entry) => entry.playedCard !== null)) {
            resolveRound(room.roomCode);
        }
    });

    function resolveRound(roomCode) {
        const room = rooms.get(roomCode);
        if (!room || room.gameState !== 'PLAYING') return;

        const activePlayers = Object.values(room.players).filter((player) => player.color !== null);
        if (activePlayers.length < MIN_PLAYERS || !activePlayers.every((player) => player.playedCard !== null)) {
            return;
        }

        const cardMap = new Map();
        activePlayers.forEach((player) => {
            const group = cardMap.get(player.playedCard) || [];
            group.push(player);
            cardMap.set(player.playedCard, group);
        });

        const validCards = [...cardMap.entries()]
            .filter(([, players]) => players.length === 1)
            .map(([value]) => value);

        const totalPotValue = room.tableScoreCards.reduce((sum, card) => sum + card.value, 0);
        const latestScoreCard = room.tableScoreCards[room.tableScoreCards.length - 1];
        let winner = null;

        if (validCards.length > 0) {
            // 이번 라운드에 공개된 카드 종류에 따라 승자를 정하고, 이월된 점수도 함께 가져갑니다.
            const winningValue = latestScoreCard.type === 'cat'
                ? Math.max(...validCards)
                : Math.min(...validCards);
            winner = cardMap.get(winningValue)[0];
            winner.score += totalPotValue;
            winner.wonCards.push(...room.tableScoreCards);
        }

        room.lastWinnerId = winner ? winner.id : null;
        room.roundResults.push({
            round: room.currentRound,
            totalValue: totalPotValue,
            cardCount: room.tableScoreCards.length,
            winner: winner
                ? winner.name + ' (' + (totalPotValue > 0 ? '+' + totalPotValue : totalPotValue) + '점 획득!)'
                : '없음 (모두 동점! 다음 판으로 이월 🔥)'
        });

        room.gameState = 'ROUND_RESULT';
        room.roundToken += 1;
        const roundToken = room.roundToken;
        broadcastRoom(room);

        setTimeout(() => {
            const currentRoom = rooms.get(roomCode);
            if (!currentRoom || currentRoom.gameState !== 'ROUND_RESULT' || currentRoom.roundToken !== roundToken) {
                return;
            }

            const currentPlayers = Object.values(currentRoom.players)
                .filter((player) => player.color !== null);

            if (currentPlayers.length < MIN_PLAYERS) {
                currentRoom.gameState = 'GAME_OVER';
                broadcastRoom(currentRoom);
                return;
            }

            if (currentRoom.currentRound >= 15 || currentRoom.scoreDeck.length === 0) {
                currentRoom.gameState = 'GAME_OVER';
                broadcastRoom(currentRoom);
                return;
            }

            currentRoom.currentRound += 1;
            const nextCard = currentRoom.scoreDeck.pop();

            if (winner) {
                currentRoom.tableScoreCards = [nextCard];
            } else {
                currentRoom.tableScoreCards.push(nextCard);
            }

            currentPlayers.forEach((player) => {
                player.playedCard = null;
            });
            currentRoom.lastWinnerId = null;
            currentRoom.gameState = 'PLAYING';
            broadcastRoom(currentRoom);
        }, 4500);
    }

    socket.on('disconnect', () => {
        const room = getCurrentRoom();
        if (!room || !room.players[socket.id]) {
            currentRoomCode = null;
            return;
        }

        const wasHost = room.hostId === socket.id;
        delete room.players[socket.id];
        currentRoomCode = null;

        if (Object.keys(room.players).length === 0) {
            clearUnoTimer(room);
            clearHalliTimer(room);
            rooms.delete(room.roomCode);
            return;
        }

        if (wasHost) {
            room.hostId = Object.keys(room.players)[0];
        }

        if (room.gameState === 'UNO_DEALING' && room.uno) {
            const uno = room.uno;
            clearUnoTimer(room);
            const oldCurrentId = uno.playerOrder[uno.currentIndex];
            uno.playerOrder = uno.playerOrder.filter((id) => id !== socket.id && room.players[id]);
            if (uno.playerOrder.length < MIN_PLAYERS) {
                uno.winnerId = uno.playerOrder[0] || null;
                uno.winnerPoints = 0;
                room.gameState = 'GAME_OVER';
                uno.lastAction = { id: ++uno.actionSequence, type: 'disconnect', playerId: socket.id };
            } else {
                uno.currentIndex = Math.max(0, uno.playerOrder.indexOf(oldCurrentId));
                uno.lastAction = { id: ++uno.actionSequence, type: 'disconnect', playerId: socket.id };
                scheduleUnoDeal(room);
            }
            broadcastRoom(room);
            return;
        }

        if (room.gameState === 'UNO_PLAYING' && room.uno) {
            const uno = room.uno;
            clearUnoTimer(room);
            const oldOrder = [...uno.playerOrder];
            const oldCurrentIndex = uno.currentIndex;
            const oldCurrentId = oldOrder[oldCurrentIndex];
            const pendingSteps = uno.pendingUnoCall?.nextSteps || 1;
            uno.playerOrder = oldOrder.filter((id) => id !== socket.id && room.players[id]);

            if (uno.playerOrder.length < MIN_PLAYERS) {
                uno.pendingUnoCall = null;
                uno.winnerId = uno.playerOrder[0] || null;
                room.gameState = 'GAME_OVER';
                uno.lastAction = { id: ++uno.actionSequence, type: 'disconnect', playerId: socket.id };
                broadcastRoom(room);
                return;
            }

            if (oldCurrentId === socket.id) {
                let nextId = null;
                for (let offset = pendingSteps; offset <= oldOrder.length + pendingSteps; offset++) {
                    const candidate = oldOrder[(oldCurrentIndex + uno.direction * offset % oldOrder.length + oldOrder.length) % oldOrder.length];
                    if (uno.playerOrder.includes(candidate)) { nextId = candidate; break; }
                }
                uno.currentIndex = Math.max(0, uno.playerOrder.indexOf(nextId));
                uno.pendingUnoCall = null;
                uno.drewCardId = null;
                uno.turnExpiresAt = Date.now() + UNO_TURN_MS;
            } else {
                uno.currentIndex = Math.max(0, uno.playerOrder.indexOf(oldCurrentId));
                if (uno.pendingUnoCall) uno.pendingUnoCall.deadline = Math.min(uno.pendingUnoCall.deadline, Date.now() + UNO_CALL_MS);
            }
            uno.lastAction = { id: ++uno.actionSequence, type: 'disconnect', playerId: socket.id };
            scheduleUnoTimer(room);
            broadcastRoom(room);
            return;
        }

        if (room.gameMode === 'HALLI' && room.halli && ['HALLI_PLAYING', 'HALLI_SETTLING'].includes(room.gameState)) {
            const halli = room.halli;
            const currentId = halli.playerOrder[halli.currentIndex];
            halli.playerOrder = halli.playerOrder.filter((id) => id !== socket.id && room.players[id]);
            halli.claims = halli.claims.filter((claim) => claim.playerId !== socket.id);
            delete halli.reactionTimes[socket.id];
            halli.currentIndex = Math.max(0, halli.playerOrder.indexOf(currentId));
            if (halli.currentIndex < 0) halli.currentIndex = 0;
            if (halli.playerOrder.length < MIN_PLAYERS) {
                const remaining = halli.playerOrder.map((id) => room.players[id]).filter(Boolean);
                halli.winnerId = remaining.sort((a, b) =>
                    ((b.halliDraw?.length || 0) + (b.halliFaceUp?.length || 0)) -
                    ((a.halliDraw?.length || 0) + (a.halliFaceUp?.length || 0))
                )[0]?.id || null;
                room.gameState = 'GAME_OVER';
                clearHalliTimer(room);
            } else if (room.gameState === 'HALLI_SETTLING' && !halli.claims.length) {
                room.gameState = 'HALLI_PLAYING';
                clearHalliTimer(room);
            } else if (currentId === socket.id) {
                halliNextTurn(room, halli.currentIndex - 1);
            }
            broadcastRoom(room);
            return;
        }

        const activePlayers = Object.values(room.players)
            .filter((player) => player.color !== null);

        if ((room.gameState === 'PLAYING' || room.gameState === 'ROUND_RESULT' || room.gameState === 'DOBBLE_PLAYING') &&
            activePlayers.length < MIN_PLAYERS) {
            room.roundToken += 1;
            room.gameState = 'GAME_OVER';
            broadcastRoom(room);
            return;
        }

        if (room.gameState === 'PLAYING' &&
            activePlayers.length >= MIN_PLAYERS &&
            activePlayers.every((player) => player.playedCard !== null)) {
            resolveRound(room.roomCode);
            return;
        }

        broadcastRoom(room);
    });
});

const PORT = process.env.PORT || 3000;
server.listen(PORT, () => {
    console.log('서버 실행 중! 포트: ' + PORT);
});

