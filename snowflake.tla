----------------------------- MODULE snowflake -----------------------------
(***************************************************************************)
(*         TLA+ specification of the Snowflake consensus algorithm         *)
(***************************************************************************)

EXTENDS Naturals, Sequences, Integers, Reals, rutschblock

\* this is essentially the slush loop    
Next ==
  /\ \E n \in Node:
    /\ Sample(n)
    /\ \E r \in 1..M:
      /\ state[n] # Uncolored
      /\ Sample(n)

=============================================================================
