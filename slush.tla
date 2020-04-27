------------------------------- MODULE slush -------------------------------
(***************************************************************************)
(*             TLA+ specification of Slush consensus algorithm             *)
(***************************************************************************)

EXTENDS Naturals, Sequences

CONSTANTS N \* the sef of all possible nodes

Node == 1 .. N \* the nodes participating

=============================================================================
