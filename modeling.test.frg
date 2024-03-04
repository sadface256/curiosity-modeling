#lang forge/bsl

open "modeling.frg"

pred alwaysInit {
    all t : TIME | init[t]
}

pred splitable[p: Player, t: TIME] {
    remainder[add[p.leftFingers, p.rightFingers], 2] = 0
}

pred everyoneCanSplit[t: TIME] {
    all p : Player | splitable[p, t]
}



//init has all ones
//turn should be 0
test suite for init {
    assert all t: TIME | oneturn[t] is necessary for init[t]

    //assert all t: TIME | init[t] is sufficient for everyoneCanSplit[t]

    assert alwaysInit is sufficient for enoughFingers


}

pred twoTurns[t1 : TIME] {
    some t2 : TIME | (t2 = t1.next and t1 != t2) implies {
        oneturn[t1] and twoturn[t2]
        or
        twoturn[t1] and oneturn[t2] 
    }
}

//the turn counter should up the next turn by one
test suite for turntaking {
    assert all t1 : TIME | turntaking[t1] is sufficient for twoTurns[t1]
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

//only ever one turn or the other turn
test suite for alwaysBalanced {
    assert whoseTurn is sufficient for alwaysBalanced

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
    assert all t1, t2 : TIME, p1, p2: Player | helperMove[p1, p2, t1, t2] is sufficient for oneThingMoved[t1, t2]
}

//the summand can't be 0
//whoevers turn it is shouldn't have just one hand change
//player can't be losing
//summand has to be on one of the player's hands
test suite for move {

}

//losing at one time plies gamestillover in the next one
//losing should be constant for all states in front of it

test suite for losing {
    //gamestillover?
}

//if nothingMoved then the game must be over
test suite for nothingMoved {

}