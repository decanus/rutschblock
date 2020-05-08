------------------------------- MODULE slush -------------------------------
(***************************************************************************)
(*           TLA+ specification of the Slush consensus algorithm           *)
(***************************************************************************)

EXTENDS Integers, Sequences

\* the K constant as specified in the paper
CONSTANT K

\* N represents the number of nodes.
CONSTANT N

\* A nodes possible states.
CONSTANT Uninitialized, Initialized

\* A nodes possible color.
CONSTANT Red, Blue, Uncolored

\* The maximum rounds
CONSTANT MAX_ROUND

\* the α constant as specified in the paper
CONSTANT Alpha

\* A nodes current state.
VARIABLE state

\* A nodes current color.
VARIABLE color

\* A nodes current round.
VARIABLE round

\* Node represents the set of nodes.
Node == 1..N

\* The set of valid node states.
State == { Uninitialized, Initialized }

\* The set of valid node colors.
Color == { Red, Blue, Uncolored }

----

Init ==
  /\ color = [i \in Node |-> Uncolored]
  /\ state = [i \in Node |-> Uninitialized]
  /\ round = [i \in Node |-> 0]

----

(***************************************************************************)
(* Node `n` receives color `c` and initializes itself with it              *)
(***************************************************************************)
ReceiveColor(n, c) ==
  /\ state[n] = Uninitialized
  /\ state' = [state EXCEPT ![n] = Initialized]
  /\ color' = [color EXCEPT ![n] = c]
  /\ UNCHANGED <<round>>

(***************************************************************************)
(* Node `n` receives a query with color `c` adds result `r`                *)
(***************************************************************************)
Query(n, c, r) ==
  /\ color' = 
     IF color[n] = Uncolored 
     THEN [color EXCEPT ![n] = c]
     ELSE color
  /\ r' = [r EXCEPT ![c] = @ + 1]

(***************************************************************************)
(* Node `n` runs an iteration of slush                                     *)
(***************************************************************************)
Slush(n) ==
  /\ round[n] < MAX_ROUND
  /\ round' = [round EXCEPT ![n] = round[n] + 1]
  /\ color[n] # Uncolored
  /\ LET \* p == [x \in DOMAIN (Node \ {n}) |-> x] \* @TODO THIS PART IS FUCKED, we need to turn the set into a tuple so we can access by key
         r == [i \in Color |-> 0]
     IN /\ \A i \in 1..K: Query(i, color[n], r) 
        /\ \A c \in Color:  color' =
         IF r[c] >= Alpha
         THEN [color EXCEPT ![n] = c]
         ELSE color
  /\ UNCHANGED <<state, color>>

Next ==
  \/ \E i \in Node, c \in Color: ReceiveColor(i, c)
  \/ \E i \in Node: Slush(i)

=============================================================================
