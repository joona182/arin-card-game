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
const MIN_PLAYERS = 2;
const CHAT_MAX_LENGTH = 200;
const CHAT_HISTORY_LIMIT = 50;
const CHAT_COOLDOWN_MS = 600;
const DOBBLE_SYMBOL_COUNT = 57;
const DOBBLE_SYMBOLS_PER_CARD = 8;
const SEAT_COLORS = new Set(['red', 'blue', 'green', 'orange', 'purple']);
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
        .trim()
        .slice(0, 10);
    return cleaned || '플레이어';
}

function shuffle(array) {
    const shuffled = [...array];
    for (let i = shuffled.length - 1; i > 0; i--) {
        const j = crypto.randomInt(i + 1);
        [shuffled[i], shuffled[j]] = [shuffled[j], shuffled[i]];
    }
    return shuffled;
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
            hand: isViewer ? [...player.hand] : [],
            playedCard: isViewer || revealCards
                ? player.playedCard
                : (player.playedCard === null ? null : 'HIDDEN'),
            wonCards: player.wonCards.map((card) => ({ ...card })),
            dobbleActiveCard: isViewer && player.dobbleStack?.length
                ? { ...player.dobbleStack[player.dobbleStack.length - 1], symbols: [...player.dobbleStack[player.dobbleStack.length - 1].symbols] }
                : null,
            dobbleCardCount: player.dobbleStack?.length || 0,
            dobbleLockMs: isViewer ? Math.max(0, (player.dobbleLockedUntil || 0) - Date.now()) : 0,
            dobbleLockVersion: isViewer ? (player.dobbleLockVersion ?? null) : null
        };
    }

    return {
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
        dobbleCardVersion: room.dobbleCardVersion || 0
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
            dobbleLockVersion: 0
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
        const gameMode = createData.gameMode === 'DOBBLE' ? 'DOBBLE' : 'EYE';
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
            dobbleCardVersion: 0
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
        if (Object.keys(room.players).length >= MAX_PLAYERS) {
            socket.emit('error-msg', '방 인원(최대 5명)이 꽉 찼어!');
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

        seatedPlayers.forEach((player) => {
            player.score = 0;
            player.hand = [];
            player.playedCard = null;
            player.wonCards = [];
            player.dobbleStack = [];
            player.dobbleLockedUntil = 0;
            player.dobbleLockVersion = 0;
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
        room.gameState = 'LOBBY';
        room.currentRound = 0;
        room.scoreDeck = [];
        room.tableScoreCards = [];
        room.lastWinnerId = null;
        room.roundResults = [];
        room.dobbleDeck = [];
        room.dobbleCenterCard = null;
        room.dobbleCardVersion = 0;

        Object.values(room.players).forEach((player) => {
            player.ready = false;
            player.score = 0;
            player.hand = [];
            player.playedCard = null;
            player.wonCards = [];
            player.dobbleStack = [];
            player.dobbleLockedUntil = 0;
            player.dobbleLockVersion = 0;
        });

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

        player.dobbleStack.push(room.dobbleCenterCard);
        player.score = player.dobbleStack.length;
        room.dobbleCenterCard = room.dobbleDeck.pop() || null;
        room.dobbleCardVersion += 1;

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
            rooms.delete(room.roomCode);
            return;
        }

        if (wasHost) {
            room.hostId = Object.keys(room.players)[0];
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

