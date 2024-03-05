#lang forge/bsl

open "modeling.frg"

pred alwaysInit {
    all t : TIME | init[t]
}

pred splitable[p: Player, t: TIME] {
    remainder[add[p.leftFingers[t], p.rightFingers[t]], 2] = 0
}

pred everyoneCanSplit[t: TIME] {
    all p : Player | splitable[p, t]
}

pred turnzero[t: TIME] {
    t.turn = 0
}

test suite for init {
    assert all t: TIME | oneturn[t] is necessary for init[t]
    assert all t: TIME | turnzero[t] is necessary for init[t]

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
    
    assert all t: TIME | init[t] is sufficient for everyoneCanSplit[t]
    assert alwaysInit is sufficient for enoughFingers

}

pred twoTurns[t1 : TIME] {
    some t2 : TIME | (t2 = t1.next and t1 != t2) implies {
        oneturn[t1] and twoturn[t2]
        or
        twoturn[t1] and oneturn[t2] 
    }
}

pred counterRises[t : TIME] {
    some t.next
    some t.turn
    t.next.turn = add[t.turn, 1]
}

//the turn counter should up the next turn by one
test suite for turntaking {
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

pred noStealingTurns {
    no t1: TIME | {
        some t1.next
        oneturn[t1]
        oneturn[t1.next]
    }
}

pred whoseTurn {
    all t: TIME | (not oneturn[t] implies twoturn[t]) and (not twoturn[t] implies oneturn[t])
}

pred balancedTurns {
    all t: TIME | alwaysBalanced and turntaking[t]
}

pred turnExists {
    all t: TIME | {
        some num: Int | num > 0 and t.turn = num
    }
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

//enforce a valid range of fingers
//at any time, fingers 0<x<4
test suite for enoughFingers {

}

//if one players turn then they should stay the same or split (so if one had changes the other should also change)
pred oneThingMoved[t, t2: TIME] {
    t.next = t2
    add[PlayerOne.leftFingers[t], PlayerOne.rightFingers[t]] != add[PlayerOne.leftFingers[t2], PlayerOne.rightFingers[t2]] implies {
        add[PlayerTwo.leftFingers[t], PlayerTwo.rightFingers[t]] = add[PlayerTwo.leftFingers[t2], PlayerTwo.rightFingers[t2]]
    }
    add[PlayerTwo.leftFingers[t], PlayerTwo.rightFingers[t]] != add[PlayerTwo.leftFingers[t2], PlayerTwo.rightFingers[t2]] implies {
        add[PlayerOne.leftFingers[t], PlayerOne.rightFingers[t]] = add[PlayerOne.leftFingers[t2], PlayerOne.rightFingers[t2]]
    }
}

//does the move-- only on an non-dead hand (though could be from a non-dead hand, move ensures nondead move)
//one thing should change
//when the turn chnages, something should have changed
test suite for helperMove {
    //assert all t1, t2 : TIME, p1, p2: Player | oneThingMoved[t1, t2] is sufficient for helperMove[p1, p2, t1, t2]
}

//the summand can't be 0
//whoevers turn it is shouldn't have just one hand change
//player can't be losing
//summand has to be on one of the player's hands
test suite for move {
    //assert all t1, t2: TIME, p1, p2 : Player, num: Int | move[t1, t2, p1, p2, num] is sufficient for oneThingMoved[t1, t2]

}

//losing at one time plies gamestillover in the next one
//losing should be constant for all states in front of it

pred stillLosing[t : TIME] {
    //if someone is losing in the state they should be losing in the next state
    some t.next
    gameStillOver[t.next]
}

pred pleasework[t: TIME] {
    noLoops[t]
    some p: Player | losing[t,p]
}

test suite for losing {
    //gamestillover?
    //assert all t: TIME | gameStillOver[t] is sufficient for pleasework[t]
    //assert all t: TIME | stillLosing[t] is necessary for gameStillOver[t]
}

pred nothingMovedTwoStates[t: TIME] {
    some t.next
    nothingMoved[t, t.next]
}

pred sumTheSame[t, t2 : TIME] {
    add[PlayerOne.rightFingers[t], PlayerOne.leftFingers[t]] = add[PlayerOne.rightFingers[t2], PlayerOne.leftFingers[t2]]
    add[PlayerTwo.rightFingers[t], PlayerTwo.leftFingers[t]] = add[PlayerTwo.rightFingers[t2], PlayerTwo.leftFingers[t2]]

}

//if nothingMoved then the game must be over
test suite for nothingMoved {
    //assert all t: TIME | nothingMovedTwoStates[t] is necessary for gameStillOver[t]
    assert all t, t2: TIME | sumTheSame[t, t2] is necessary for nothingMoved[t, t2]

}