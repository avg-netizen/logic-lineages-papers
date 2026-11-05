# Cipher all-ones equations: uniqueness only

This component supports the cipher arithmetic dependency used by paper 02 finite-bare hardness and paper 09 functional hardness. It uses the unchanged actual natural-number bitwise AND and the original OnesEquations from CipherDefinitions/CipherTargets.

Two exact targets prove unconditional uniqueness of an even natural masked-square fixed point and at most one pair of natural solutions to the unchanged cipher all-ones equations. The fixed-point theorem uses the actual Nat bitwise AND with no finiteness bound or assumed digit representation. The arithmetic equation uniqueness is conditional on two solutions existing; no solution or equality to the sparse all-ones sums is established by this component.

The three accepted component files import the separately frozen CipherOnesTargets statement supplier, which defines the forward sparse-sum and full-characterization propositions but does not prove them. That exact supplier is included because it is needed by the checked import closure. No full-characterization proof or gate is imported or accepted.

The original n/q conditions remain inside OnesEquations. This at-most-one result does not show that the sparse sums solve the equations, that a solution exists, or that every solution has the intended digit interpretation. Ones-Diophantineness, variable bounded-universal closure, MRDP, genuine undecidability and whole-source hardness remain pending. No numbered statement is promoted.
