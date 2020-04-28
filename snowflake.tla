----------------------------- MODULE snowflake -----------------------------
(***************************************************************************)
(*         TLA+ specification of the Snowflake consensus algorithm         *)
(***************************************************************************)

EXTENDS Naturals, Sequences, Integers, Reals, rutschblock

\* the counts for nodes
VARIABLE count

----

Init ==
  /\ state = [i \in Node |-> Uncolored]
  /\ responses = [i \in Node |-> [c \in Colors |-> 0]]
  /\ queries = [i \in Node |-> {}]
  /\ count = [i \in Node |-> 0]

----

=============================================================================
