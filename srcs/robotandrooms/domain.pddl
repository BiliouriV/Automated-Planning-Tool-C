(define (domain RobotAndRooms)

(:requirements :strips :negative-preconditions :conditional-effects :typing :action-costs)

(:types
    room - room window - window
)
(:predicates
    (isIn ?x - room)
		(hasDoor ?x ?y - room)
		(isOpen ?x - window)
    (isWindowIn ?x - window ?y - room)

)
(:functions
    (total-cost) - number
)

(:action move
:parameters (?x - room ?y - room)
:precondition (and (isIn ?x) (hasDoor ?x ?y) (not (isIn ?y))
:effect (and (isIn ?y) (not (isIn ?x)) (increase (total-cost) 3))
)

(:action open
  :parameters (?x - window ?y - room)
  :precondition (and (isWindowIn ?x ?y) (isIn ?y) (not (isOpen ?x)))
  :effect (and (isOpen ?x) (increase (total-cost) 1)))
)
