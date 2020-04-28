------------------------------- MODULE slush -------------------------------
(***************************************************************************)
(*           TLA+ specification of the Slush consensus algorithm           *)
(***************************************************************************)

EXTENDS rutschblock

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

(***************************************************************************)
(* Run slush for node `n`                                                  *)
(***************************************************************************)
Loop(n) ==
    /\ Sample(n)
    /\ \E r \in 1..M:
      /\ state[n] # Uncolored
      /\ Sample(n)

\* this is essentially the slush loop    
\* may want to put this into a seperate function
Next ==
  /\ \E n \in Node:
    /\ Loop(n)
      
vars == <<state, responses, queries>>      

Spec == Init /\ [][Next]_vars

=============================================================================
