---- MODULE traffic_light ----

VARIABLE color

TypeOk == color \in {"red", "green", "yellow"}

Init == color = "red"

TurnGreen ==
    /\ color = "red"
    /\ color' = "green"

TurnYellow ==
    /\ color = "green"
    /\ color' = "yellow"

TurnRed ==
    /\ color = "yellow"
    /\ color' = "green"

Next ==
    \/ TurnGreen \/ TurnYellow \/ TurnRed

Spec == Init /\ [][Next]_color

====
