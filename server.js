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
            wonCards: player.wonCards.map((card) => ({ ...card }))
        };
    }

    return {
        roomCode: room.roomCode,
        hostId: room.hostId,
        players,
        gameState: room.gameState,
        currentRound: room.currentRound,
        scoreDeck: [],
        tableScoreCards: room.tableScoreCards.map((card) => ({ ...card })),
        lastWinnerId: room.lastWinnerId,
        roundResults: room.roundResults.map((result) => ({ ...result }))
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
            wonCards: []
        };
        broadcastRoom(room);
    }

    function requireHost(room) {
        if (room.hostId !== socket.id) {
            socket.emit('error-msg', '이 기능은 방장만 사용할 수 있어!');
            return false;
        }
        return true;
    }

    socket.on('create-room', (name) => {
        if (rejectIfAlreadyInRoom()) return;

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
            players: {},
            gameState: 'LOBBY',
            currentRound: 0,
            scoreDeck: [],
            tableScoreCards: [],
            lastWinnerId: null,
            roundResults: [],
            roundToken: 0
        };
        rooms.set(roomCode, room);
        joinRoomLogic(room, name);
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
        room.gameState = 'PLAYING';
        room.currentRound = 1;
        room.scoreDeck = shuffle(INITIAL_SCORE_DECK);
        room.tableScoreCards = [room.scoreDeck.pop()];
        room.lastWinnerId = null;
        room.roundResults = [];

        seatedPlayers.forEach((player) => {
            player.score = 0;
            player.hand = newHand();
            player.playedCard = null;
            player.wonCards = [];
        });

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

        Object.values(room.players).forEach((player) => {
            player.ready = false;
            player.score = 0;
            player.hand = [];
            player.playedCard = null;
            player.wonCards = [];
        });

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

        if ((room.gameState === 'PLAYING' || room.gameState === 'ROUND_RESULT') &&
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

