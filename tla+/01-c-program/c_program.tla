---- MODULE c_program ----

EXTENDS Integers

VARIABLES i, pc

Init == /\ i = 0 
        /\ pc = "start"

Next == \/ /\ pc = "start"
           /\ pc' = "middle"
           /\ i' \in 0..1000
        \/ /\ pc = "middle"
           /\ pc' = "done"
           /\ i' = i + 1

====
