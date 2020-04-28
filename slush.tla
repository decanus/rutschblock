------------------------------- MODULE slush -------------------------------
(***************************************************************************)
(*           TLA+ specification of the Slush consensus algorithm           *)
(***************************************************************************)

EXTENDS Naturals, Sequences, Integers, Reals

\* the K constant as specified in the paper
CONSTANT K

\* the M constant as specified in the paper
CONSTANT M

\* the α constant as specified in the paper
CONSTANT Alpha

\* the sum of nodes participating in consensus
CONSTANT N

\* Server states
CONSTANTS Red, Blue, Uncolored

\* the nodes state
VARIABLE state

\* the responses a node receives
VARIABLE responses

\* the queries for a specific node
VARIABLE queries

\* the set of colors
Colors == { Red, Blue }

\* the sef of all possible nodes
Node == 1 .. N

----

TypeOK ==
  /\ Alpha > K / 2
  
ASSUME ConstantTypes ==
  /\ K \in Int
  /\ M \in Int
  /\ Alpha \in Int
  /\ N \in Int

----

----

Init ==
  /\ state = [i \in Node |-> Uncolored]
  /\ responses = [i \in Node |-> [c \in Colors |-> 0]]
  /\ queries = [i \in Node |-> {}]

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

(***************************************************************************)
(* Node `n` sends a query to `r` with color `c`                            *)
(***************************************************************************)
Query(n, r, c) ==
  /\ queries' = [queries EXCEPT ![r] = Append(@, [node |-> n, color |-> c])]

(***************************************************************************)
(* Node `n` processes its current queries                                  *)
(***************************************************************************)
ProcessQueries(n) ==
  /\ \E q \in queries[n]:
      OnQuery(n, q.node, q.color)
  /\  queries' = [queries EXCEPT ![n] = {}]

(***************************************************************************)
(* Node `n` samples other nodes                                            *)
(***************************************************************************)
Sample(n) ==
  /\ \E r \in 1..K:
      Query(n, r, state[r])
  /\ \E c \in Colors:
      /\ state' =
         IF responses[n][c] >= Alpha
         THEN [state EXCEPT ![n] = c]
         ELSE state
      /\ responses' = [responses EXCEPT ![n][c] = 0]

\* this is essentially the slush loop    
Next ==
  /\ \E n \in Node:
    /\ Sample(n)
    /\ \E r \in 1..M:
      /\ state[n] # Uncolored
      /\ Sample(n)
      
vars == <<state, responses, queries>>      

Spec == Init /\ [][Next]_vars

=============================================================================
