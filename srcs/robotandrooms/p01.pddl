(define (problem W1-2-3)
(:domain RobotAndRooms)
(:objects
  rm1 rm2 - room
  w1 w2 w3 - window
 )

(:init
    (isIn rm1)
    (isWindowIn w1 rm1)
    (isWindowIn w2 rm1)
    (isWindowIn w3 rm2)
    (hasDoor rm1 rm2)
    (hasDoor rm2 rm1)
    (hasDoor rm3 rm2)
    (hasDoor rm2 rm3)
    (isOpen w2)

(:goal (and (isOpen w1) (isOpen w2) (isOpen w3))))
