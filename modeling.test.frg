#lang forge/bsl

open "modeling.frg"

//just for testing, every state is init
pred alwaysInit {
    all t : TIME | init[t]
}

//possible to split on a hand with a sum that's even
pred splitable[p: Player, t: TIME] {
    remainder[add[p.leftFingers[t], p.rightFingers[t]], 2] = 0
}

pred everyoneCanSplit[t: TIME] {
    all p : Player | splitable[p, t]
}

//just ensures the turn is 0 lol
pred turnzero[t: TIME] {
    t.turn = 0
}

test suite for init {
    //the first turn is always player one's
    //turn should always be 0
    assert all t: TIME | oneturn[t] is necessary for init[t]
    assert all t: TIME | turnzero[t] is necessary for init[t]

    //this is just what the init case should look like
    example baseGame is {some t: TIME | init[t]} for {
        PlayerOne = `PlayerOne0
        PlayerTwo = `PlayerTwo0
        Player = `PlayerOne0 + `PlayerTwo0
        TIME = `time0
        `PlayerOne0.leftFingers = `time0 -> 1
        `PlayerOne0.rightFingers = `time0 -> 1
        `PlayerTwo0.leftFingers = `time0 -> 1
        `PlayerTwo0.rightFingers = `time0 -> 1
    }
    
    //the sum of everyone's hands should be even if theyre all 1
    assert all t: TIME | init[t] is sufficient for everyoneCanSplit[t]
    //all hands = 1 should ensure the 0<x<4 predicate
    assert alwaysInit is sufficient for enoughFingers

}

//one turn follows the next turn
pred twoTurns[t1 : TIME] {
    some t2 : TIME | (t2 = t1.next and t1 != t2) implies {
        oneturn[t1] and twoturn[t2]
        or
        twoturn[t1] and oneturn[t2] 
    }
}

//the next turn should have their turn counter one more than the last turn
pred counterRises[t : TIME] {
    some t.next
    some t.turn
    t.next.turn = add[t.turn, 1]
}

//the turn counter should up the next turn by one
test suite for turntaking {
    //if turn taking happens, then the turns have changed (remainder 1 vs remainder 0)
    assert all t1 : TIME | turntaking[t1] is sufficient for twoTurns[t1]

    example uppedCounter is {some t: TIME | turntaking[t]} for {
        PlayerOne = `PlayerOne0
        PlayerTwo = `PlayerTwo0
        Player = `PlayerOne0 + `PlayerTwo0
        TIME = `time0 + `time1
        `time0.next = `time1
        `time0.turn = 0
        `time1.turn = 1
    }
    
    assert all t1 : TIME | turntaking[t1] is necessary for counterRises[t1]
}

//the same person shouldn't go twice
pred noStealingTurns {
    no t1: TIME | {
        some t1.next
        oneturn[t1]
        oneturn[t1.next]
    }
}

//if its not my turn its your turn and vice versa
pred whoseTurn {
    all t: TIME | (not oneturn[t] implies twoturn[t]) and (not twoturn[t] implies oneturn[t])
}

//if we're incrementing, then we should be balanced
pred balancedTurns {
    all t: TIME | alwaysBalanced and turntaking[t]
}

//every time should have something in the turn (made pos bc -7/2 has a remainder of -1????)
pred turnExists {
    all t: TIME | {
        some num: Int | num > 0 and t.turn = num
    }
}

pred sameTurn[t1, t2 : TIME] {
    some t1.turn and some t2.turn
    t1.next = t2
    t1 != t2
    (oneturn[t1] and oneturn[t2]) or (twoturn[t1] and twoturn[t2])
}

pred notSameTurn[t1, t2 : TIME] {
    not sameTurn[t1, t2]
}

test suite for alwaysBalanced {
    assert whoseTurn is sufficient for alwaysBalanced
    assert whoseTurn is necessary for balancedTurns
    assert all t: TIME | noStealingTurns is necessary for balancedTurns
    assert turnExists is sufficient for alwaysBalanced

    example basicBalance is {alwaysBalanced} for {
        PlayerOne = `PlayerOne0
        PlayerTwo = `PlayerTwo0
        Player = `PlayerOne0 + `PlayerTwo0
        TIME = `time0 + `time1
        `time0.next = `time1
        `time0.turn = 0
        `time1.turn = 1
    }
}

//if one players turn then they should stay the same or split (so if one had changes the other should also change)
pred oneThingMoved[t, t2: TIME] {
    add[PlayerOne.leftFingers[t], PlayerOne.rightFingers[t]] != add[PlayerOne.leftFingers[t2], PlayerOne.rightFingers[t2]] implies {
        add[PlayerTwo.leftFingers[t], PlayerTwo.rightFingers[t]] = add[PlayerTwo.leftFingers[t2], PlayerTwo.rightFingers[t2]]
    }
    add[PlayerTwo.leftFingers[t], PlayerTwo.rightFingers[t]] != add[PlayerTwo.leftFingers[t2], PlayerTwo.rightFingers[t2]] implies {
        add[PlayerOne.leftFingers[t], PlayerOne.rightFingers[t]] = add[PlayerOne.leftFingers[t2], PlayerOne.rightFingers[t2]]
    }
}

pred somethingMoved[t1, t2 : TIME] {
    not {
        add[PlayerTwo.leftFingers[t1], PlayerTwo.rightFingers[t1]] = add[PlayerTwo.leftFingers[t2], PlayerTwo.rightFingers[t2]] and
        add[PlayerOne.leftFingers[t1], PlayerOne.rightFingers[t1]] = add[PlayerOne.leftFingers[t2], PlayerOne.rightFingers[t2]]
    }
}

//something changes and only one thing changes
test suite for helperMove {
    assert all t1, t2 : TIME, p1, p2: Player | oneThingMoved[t1, t2] is necessary for helperMove[p1, p2, t1, t2]

    //good move
    example exampleMove is {some t1, t2 : TIME, p1, p2: Player | helperMove[p1, p2, t1, t2]} for {
        PlayerOne = `PlayerOne0
        PlayerTwo = `PlayerTwo0
        Player = `PlayerOne0 + `PlayerTwo0
        TIME = `time0 + `time1
        `PlayerOne0.leftFingers = `time0 -> 1 + `time1 -> 1
        `PlayerOne0.rightFingers = `time0 -> 1 + `time1 -> 1
        `PlayerTwo0.leftFingers = `time0 -> 1 + `time1 -> 1
        `PlayerTwo0.rightFingers = `time0 -> 1 + `time1 -> 2
    }

    //cant move on a dead hand
    example helpingTheEnemy is {some t1, t2 : TIME, p1, p2: Player | not helperMove[p1, p2, t1, t2]} for {
        PlayerOne = `PlayerOne0
        PlayerTwo = `PlayerTwo0
        Player = `PlayerOne0 + `PlayerTwo0
        TIME = `time0 + `time1
        `PlayerOne0.leftFingers = `time0 -> 1 + `time1 -> 1
        `PlayerOne0.rightFingers = `time0 -> 1 + `time1 -> 1
        `PlayerTwo0.leftFingers = `time0 -> 0 + `time1 -> 1
        `PlayerTwo0.rightFingers = `time0 -> 1 + `time1 -> 1
    }

    //only one hand should change
    example clearlyCheating is {some t1, t2 : TIME, p1, p2: Player | not helperMove[p1, p2, t1, t2]} for {
        PlayerOne = `PlayerOne0
        PlayerTwo = `PlayerTwo0
        Player = `PlayerOne0 + `PlayerTwo0
        TIME = `time0 + `time1
        `PlayerOne0.leftFingers = `time0 -> 1 + `time1 -> 1
        `PlayerOne0.rightFingers = `time0 -> 1 + `time1 -> 1
        `PlayerTwo0.leftFingers = `time0 -> 4 + `time1 -> 1
        `PlayerTwo0.rightFingers = `time0 -> 3 + `time1 -> 1
    }
}


//the summand can't be 0
pred notZero[num: Int] {
    num != 0
}
//player can't be losing
pred notLosing[t: TIME, p: Player] {
    not losing[t, p]
}
//summand has to be on one of the player's hands
pred onAHand[num: Int, t: TIME] {
    PlayerOne.leftFingers[t] = num or
    PlayerOne.rightFingers[t] = num or
    PlayerTwo.leftFingers[t] = num or
    PlayerTwo.rightFingers[t] = num
}

test suite for move {
    assert all t1, t2: TIME, p1, p2 : Player, num: Int | notLosing[t1, p1] is necessary for move[t1, t2, p1, p2, num]
    assert all t1, t2: TIME, p1, p2 : Player, num: Int | notZero[num] is necessary for move[t1, t2, p1, p2, num]
    assert all t1, t2: TIME, p1, p2 : Player, num: Int | onAHand[num, t1] is necessary for move[t1, t2, p1, p2, num]
    example exampleBigMove is {some t1, t2 : TIME, p1, p2: Player, num: Int | move[t1, t2, p1, p2, num]} for {
        PlayerOne = `PlayerOne0
        PlayerTwo = `PlayerTwo0
        Player = `PlayerOne0 + `PlayerTwo0
        TIME = `time0 + `time1
        `PlayerOne0.leftFingers = `time0 -> 1 + `time1 -> 1
        `PlayerOne0.rightFingers = `time0 -> 1 + `time1 -> 1
        `PlayerTwo0.leftFingers = `time0 -> 1 + `time1 -> 1
        `PlayerTwo0.rightFingers = `time0 -> 1 + `time1 -> 2
    }

    example exampleSplitting is {some t1, t2 : TIME, p1, p2: Player, num: Int | move[t1, t2, p1, p2, num]} for {
        PlayerOne = `PlayerOne0
        PlayerTwo = `PlayerTwo0
        Player = `PlayerOne0 + `PlayerTwo0
        TIME = `time0 + `time1
        `PlayerOne0.leftFingers = `time0 -> 1 + `time1 -> 1
        `PlayerOne0.rightFingers = `time0 -> 1 + `time1 -> 1
        `PlayerTwo0.leftFingers = `time0 -> 3 + `time1 -> 2
        `PlayerTwo0.rightFingers = `time0 -> 1 + `time1 -> 2
    }

    example badSplitting is {some t1, t2 : TIME, p1, p2: Player, num: Int | not move[t1, t2, p1, p2, num]} for {
        PlayerOne = `PlayerOne0
        PlayerTwo = `PlayerTwo0
        Player = `PlayerOne0 + `PlayerTwo0
        TIME = `time0 + `time1
        `PlayerOne0.leftFingers = `time0 -> 1 + `time1 -> 1
        `PlayerOne0.rightFingers = `time0 -> 1 + `time1 -> 1
        `PlayerTwo0.leftFingers = `time0 -> 3 + `time1 -> 1
        `PlayerTwo0.rightFingers = `time0 -> 2 + `time1 -> 4
    }
}

pred allLosing[t: TIME] {
    all t: TIME {
        some t2: TIME, p: Player | losing[t2, p] implies reachable[t, t2, next] and losing[t, p]
    }
}

pred stillLosing[t : TIME] {
    some t.next => {some p : Player | losing[t.next, p]}
}

pred zerosum[t: TIME, p: Player] {
    add[p.leftFingers[t], p.rightFingers[t]] = 0
}

test suite for losing {
    assert all t: TIME, p: Player | zerosum[t, p] is necessary for losing[t, p]
    assert all t: TIME | stillLosing[t] is necessary for gameStillOver[t]
    example oneLoss is {some t1 : TIME, p: Player | losing[t1, p]} for {
        PlayerOne = `PlayerOne0
        PlayerTwo = `PlayerTwo0
        Player = `PlayerOne0 + `PlayerTwo0
        TIME = `time0
        `PlayerOne0.leftFingers = `time0 -> 0 
        `PlayerOne0.rightFingers = `time0 -> 0 
        `PlayerTwo0.leftFingers = `time0 -> 4 
        `PlayerTwo0.rightFingers = `time0 -> 5 
    }

    example negHand is {some t1 : TIME, p: Player | not losing[t1, p]} for {
        PlayerOne = `PlayerOne0
        PlayerTwo = `PlayerTwo0
        Player = `PlayerOne0 + `PlayerTwo0
        TIME = `time0
        `PlayerOne0.leftFingers = `time0 -> -1 
        `PlayerOne0.rightFingers = `time0 -> -1 
        `PlayerTwo0.leftFingers = `time0 -> 4 
        `PlayerTwo0.rightFingers = `time0 -> 5 
    }
}

pred nothingMovedTwoStates[t: TIME] {
    some t.next => nothingMoved[t, t.next]
}

pred sumTheSame[t, t2 : TIME] {
    add[PlayerOne.rightFingers[t], PlayerOne.leftFingers[t]] = add[PlayerOne.rightFingers[t2], PlayerOne.leftFingers[t2]]
    add[PlayerTwo.rightFingers[t], PlayerTwo.leftFingers[t]] = add[PlayerTwo.rightFingers[t2], PlayerTwo.leftFingers[t2]]

}


//if nothingMoved then the game must be over
test suite for nothingMoved {
    assert all t: TIME | nothingMovedTwoStates[t] is necessary for gameStillOver[t]
    assert all t, t2: TIME | sumTheSame[t, t2] is necessary for nothingMoved[t, t2]
    //assert all t, t2: TIME | sameTurn[t, t2] is necessary for nothingMoved[t, t2]
    example everyHandDead is {some t1, t2 : TIME | nothingMoved[t1, t2]} for {
        PlayerOne = `PlayerOne0
        PlayerTwo = `PlayerTwo0
        Player = `PlayerOne0 + `PlayerTwo0
        TIME = `time0 + `time1
        `PlayerOne0.leftFingers = `time0 -> 0 + `time1 -> 0
        `PlayerOne0.rightFingers = `time0 -> 0 + `time1 -> 0
        `PlayerTwo0.leftFingers = `time0 -> 0 + `time1 -> 0
        `PlayerTwo0.rightFingers = `time0 -> 0 + `time1 -> 0
    }

    example oneHandLives is {some t1, t2 : TIME | not nothingMoved[t1, t2]} for {
        PlayerOne = `PlayerOne0
        PlayerTwo = `PlayerTwo0
        Player = `PlayerOne0 + `PlayerTwo0
        TIME = `time0 + `time1
        `PlayerOne0.leftFingers = `time0 -> 0 + `time1 -> 1
        `PlayerOne0.rightFingers = `time0 -> 0 + `time1 -> 0
        `PlayerTwo0.leftFingers = `time0 -> 0 + `time1 -> 0
        `PlayerTwo0.rightFingers = `time0 -> 0 + `time1 -> 0
    }
}