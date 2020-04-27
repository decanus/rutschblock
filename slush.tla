------------------------------- MODULE slush -------------------------------
(***************************************************************************)
(*             TLA+ specification of Slush consensus algorithm             *)
(***************************************************************************)

EXTENDS Naturals, Sequences

\* the sef of all possible nodes
CONSTANTS Node

\* Server states
CONSTANTS Red, Blue, Uncolored

\* the nodes state
VARIABLE state

Colors == { Red, Blue }

----
Init == /\ state = [i \in Node |-> Uncolored]

----

=============================================================================
