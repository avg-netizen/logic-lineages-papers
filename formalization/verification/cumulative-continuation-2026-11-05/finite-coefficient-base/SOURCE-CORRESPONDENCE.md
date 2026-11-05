# Finite-coefficient source scalar bridge

Paper08 `thm:finite-source` and its proof, paper.tex lines194–234, replace every
finite closed coefficient k by the literal BASE expression f^[k](g+2k)+k. The
actual collapse identity is already proved in ActualFiniteHead. This component
uses the ORIGINAL ForwardTranslation.Scalar and ClosedPositive syntax and their
existing scalarSyntaxCode and closedPositiveCode encoders.

The coefficient recognizer evaluates one/add/emul and rejects literal Omega.
Soundness identifies every returned integer with the actual normal-ordinal value.
It does not claim completeness for all semantically finite presentations. The
recognized original scalar is compiled to literal BaseTerm syntax with unchanged
variable indices and exact support. Natural-product omega times a finite ordinal
is connected to ordinary ordinal omega*k by the existing checked arithmetic lemma.

The original-source endpoint uses the actual canonical default-policy assignment,
all-ground free context and literal recursor absence. Existing assignment no-Omega
and source forward-translation theorems discharge acceptance of its actual scalar
coordinate, without an internal type bound or assumed successful new compiler.
The existing raw variable index map is used; no independent coordinate values are
introduced. Semantic equality holds at every indexed Nat valuation and hence at
positive valuations.

The seven targets separate coefficient soundness, actual expansion identity,
scalar semantics/support, no-Omega source completeness, recursor-free actual source,
literal existing-code calibration and total numeric programs. This advances the
scalar translation and recursor-free part of the printed proof. Completeness for
the full semantic finite-coefficient class and the final vector weak/WW-strict/
equality decision consumer remain separate. No whole theorem promotion is claimed.
