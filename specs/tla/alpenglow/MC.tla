---------------------------- MODULE MC ----------------------------
(***************************************************************************
 * Model checking configuration module for Alpenglow
 * This module defines concrete values for model checking
 ***************************************************************************)
EXTENDS MainProtocol, TLC

\* Define concrete StakeMap function for model checking
MC_StakeMap == [v \in Validators |-> 25]

=============================================================================