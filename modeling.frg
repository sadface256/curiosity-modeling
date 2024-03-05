#lang forge/bsl

//each term is abstracted out to a time, that has a next term and a turn counter
sig TIME{
    next: lone TIME,
    turn: one Int
}

//there are two players, each with two hands, that at each time have a certain number of fingers up
abstract sig Player {
    leftFingers: pfunc TIME -> Int,
    rightFingers: pfunc TIME -> Int
}

one sig PlayerOne extends Player {}

one sig PlayerTwo extends Player {}

//initial-> everyone start with one
pred init[t: TIME] {
    all p: Player | p.leftFingers[t] = 1 and p.rightFingers[t] = 1
    t.turn = 0
}

//there should never be a time where a player has more than 4 fingers up or less than 0 fingers up
pred enoughFingers {
    no t: TIME, p: Player | {
        p.leftFingers[t] < 0 or
        p.leftFingers[t] > 4 or
        p.rightFingers[t] < 0 or
        p.rightFingers[t] > 4
    }
}
//no infinite loops, but ends after 10 times anyway

pred noLoops[t: TIME]{
    some t.next => t.next != t
}

//ups the turn counter
pred turntaking[t: TIME] {
   some t.next implies t.next.turn = add[t.turn, 1]
}

//can either be player ones or player twos turn, as determined by the turn counter
pred oneturn[t : TIME] {
    remainder[t.turn, 2] = 0
}

pred twoturn[t: TIME] {
    remainder[t.turn, 2] = 1
}

pred balanced[t: TIME] {
    oneturn[t] or twoturn[t]
}

pred alwaysBalanced {
    all t: TIME | balanced[t]
}

//a player loses if both of their hands have been reduced to 0
pred losing[t: TIME, p: Player] {
    p.leftFingers[t] = 0 and p.rightFingers[t] = 0
}

pred move[t1, t2: TIME, playing, receiving: Player, summand: Int] {
    --guard: conditions
    --has to be players turn (1 goes first)
    oneturn[t1] implies {playing = PlayerOne and receiving = PlayerTwo}
    twoturn[t1] implies {playing = PlayerTwo and receiving = PlayerOne}
    --summand has to be on the moving player
    summand = playing.leftFingers[t1] or summand = playing.rightFingers[t1]
    --summand cannot be 0 (can't play dead hand)
    summand != 0

    --if someone's losing, no one moves
    all p: Player | not losing[t1, p]

    --splitting is possible when the sum of your hands is even
    remainder[add[playing.leftFingers[t1], playing.rightFingers[t1]], 2] = 0 implies {
        --a split happens and nothing else changes
        {
            playing.leftFingers[t2] = divide[add[playing.leftFingers[t1], playing.rightFingers[t1]], 2]
            playing.rightFingers[t2] = divide[add[playing.leftFingers[t1], playing.rightFingers[t1]], 2]
            receiving.leftFingers[t2] = receiving.leftFingers[t1]
            receiving.rightFingers[t2] = receiving.rightFingers[t1]
        }
        or
        --a move happens and nothing else changes
        {
            helperMove[playing, receiving, t1, t2] and not nothingMoved[t1, t2]
        }

    }

    remainder[add[playing.leftFingers[t1], playing.rightFingers[t1]], 2] = 1 implies {
        --a move happens and nothing else changes
        helperMove[playing, receiving, t1, t2] and not nothingMoved[t1, t2]
    }
}


pred helperMove[player, receiving : Player, t1, t2: TIME] {
    {
        receiving.leftFingers[t1] != 0
        player.leftFingers[t2] = player.leftFingers[t1]
        player.rightFingers[t2] = player.rightFingers[t1]
        receiving.leftFingers[t2] = fingerSum[receiving.leftFingers[t1], player.leftFingers[t1]]
        receiving.rightFingers[t2] = receiving.rightFingers[t1]
    }
    or
    {
        receiving.rightFingers[t1] != 0
        player.leftFingers[t2] = player.leftFingers[t1]
        player.rightFingers[t2] = player.rightFingers[t1]
        receiving.leftFingers[t2] = receiving.leftFingers[t1]
        receiving.rightFingers[t2] = fingerSum[receiving.rightFingers[t1], player.leftFingers[t1]]
    }
    or
    {
        receiving.leftFingers[t1] != 0 
        player.leftFingers[t2] = player.leftFingers[t1]
        player.rightFingers[t2] = player.rightFingers[t1]
        receiving.leftFingers[t2] = fingerSum[receiving.leftFingers[t1], player.rightFingers[t1]]
        receiving.rightFingers[t2] = receiving.rightFingers[t1]
    }
    or
    {
        receiving.rightFingers[t1] != 0
        player.leftFingers[t2] = player.leftFingers[t1]
        player.rightFingers[t2] = player.rightFingers[t1]
        receiving.leftFingers[t2] = receiving.leftFingers[t1]
        receiving.rightFingers[t2] = fingerSum[receiving.rightFingers[t1], player.rightFingers[t1]]
    }
}

pred nothingMoved[t1, t2: TIME] {
    PlayerOne.leftFingers[t2] = PlayerOne.leftFingers[t1]
    PlayerOne.rightFingers[t2] = PlayerOne.rightFingers[t1]
    PlayerTwo.leftFingers[t2] = PlayerTwo.leftFingers[t1]
    PlayerTwo.rightFingers[t2] = PlayerTwo.rightFingers[t1]
}

fun fingerSum[int1, int2: Int]: one Int {
    (add[int1, int2] > 4 or add[int1, int2] < 0) implies 0 else add[int1, int2]
}

//if a game ended, everything should stay the same
pred gameStillOver[t1: TIME] {
    some p: Player | losing[t1, p]

    some t1.next => nothingMoved[t1, t1.next]

    // PlayerOne.leftFingers[t1] = PlayerOne.leftFingers[t1.next]
    // PlayerOne.rightFingers[t1] = PlayerOne.rightFingers[t1.next]
    // PlayerTwo.leftFingers[t1] = PlayerTwo.leftFingers[t1.next]
    // PlayerTwo.rightFingers[t1] = PlayerTwo.rightFingers[t1.next]
}

pred someoneLoses {
    some t: TIME, p: Player | {
        losing[t, p]
        some t.next
    }
}

pred traces {
    enoughFingers
    alwaysBalanced

    some firstState: TIME | some lastState: TIME | {
        init[firstState]
        no t: TIME | t.next = firstState
        no lastState.next
        all t: TIME | t != lastState implies {
            turntaking[t]
            (some p, r: Player, s: Int | move[t, t.next, p, r, s]) or gameStillOver[t]
        }
    }

}

run {traces} for 9 TIME for {next is linear}

//run {traces someoneLoses} for 9 TIME for {next is linear}