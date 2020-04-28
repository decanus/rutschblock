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

\* the responses a node receives
VARIABLE responses

Colors == { Red, Blue }

----
Init ==
  /\ state = [i \in Node |-> Uncolored]
  /\ responses = [i \in Node |-> [c \in Colors |-> 0]]

----

(***************************************************************************)
(* Respond to `r` with a color `c`                                         *)
(***************************************************************************)
Respond(r, c) ==
  /\ responses' = [responses EXCEPT ![r][c] = responses[r][c] + 1]

(***************************************************************************)
(* Node `n` receives a query from `s` with color `c`                       *)
(***************************************************************************)
OnQuery(n, s, c) ==
  /\ state' =
     IF state[n] = Uncolored
     THEN [state EXCEPT ![n] = c]
     ELSE state
  /\ Respond(s, state[n])

=============================================================================
