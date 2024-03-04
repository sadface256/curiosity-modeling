# Project Objective

I'm modeling the game sticks, which is a game played with two people. Each person starts with one finger up. As players take turns, they hit other players hands, adding what's on their hand to the player's hand they tapped. (i hit my left hand(2) with ur right hand(1), and now you have 3 on your right hand). If a player ever gets 5 or more on their hand, that hand is dead. When the fingers up on both hands are even, a player can evenly distribute fingers to both hands (4 -> 2 and 2). A player wins when both of their opponent's hands are dead.

# Model Design and Visualization

My model abstracts each time as a TIME unit, which keeps track of how many turns have passed. Two players have two hands, each that map a TIME to the amount of fingers they have on that hand at that time. The run statement makes a trace of games that run linearly. The visualizer is broken for this to be honest? I would just look at the table and dream to figure out what does what at what time. I didn't make a visualizer for this project. If you were to use to visualizer you'd see a list of time elements, and with the time projection you'd see each player ad the amount of fingers they have on that hand.

# Signatures and Predicates
Each TIME is a turn, and the two players are, well, two players. The init predicate starts it normal, and enoughFingers guarantees that the numbers continue to be good. Turntaking updates the turn counter, and there are other predicates that decide whose turn it is (and it's always going to be someone's turn). I used a turn counter since unlike tic tac toe, there was no way in the game Losing is a predicate that figures out if a player has two dead hands. gameStillOver ensures if someone is losing, nothing happens in the game. The move predicate is a little complex, but essentially it takes one of the playing character's fingers and adds them to one of the other player's fingers. It also allows for splitting in that predicate, but i split the main movement (just tapping someone's hand) into a seperate helper. Traces just initializes a game set with turns that go one after another.

# Testing
