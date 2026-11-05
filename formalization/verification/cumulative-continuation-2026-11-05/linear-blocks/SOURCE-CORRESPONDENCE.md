# Source correspondence: linear quantified row blocks

## Original syntax and semantics

This package composes the already checked `LinearRows.eliminate` operation. It
uses the unchanged `NormalForm.Formula`, `Summand`, `Formula.eval`, and
`NormalForm.existsPrefix`. Thus the input is still an integer constant plus a
finite list of weighted variable, shifted-Phi, or hyper-Phi summands, arranged in
arbitrary Boolean combinations of nonnegative and positive-modulus divisibility
atoms. Original guards remain ordinary formulas at their original Boolean positions.

The fragment test is `names.all (fun i => LinearRows.isLinear i p)`. It inspects
the original matrix, including coefficient-zero nonlinear occurrences. It neither
assumes a successful elimination result nor introduces independent witnesses for
nonlinear parameter values. No distinct-name or nonempty-prefix premise is added.

## The missing composition invariant

A one-name elimination result alone does not justify applying it to a second name:
the second call's linearity premise must be established for the actual intermediate
formula. The new exact summand-membership theorem supplies that invariant:

`s in occurrences (LinearRows.eliminate i p)` iff
`s.name != i` and `s in occurrences p`.

This theorem has no linearity premise. Row scaling keeps the actual summand list
even at scale zero, adjustment retains the literal remainders, and every instantiated
normalized atom retains its residual summands. The zero cutoff/residue is present
because the period is positive. Both directions of membership are proved. The
statement concerns membership, not unchanged list order or multiplicity.

Consequently the output's linearity test at `j` is true when `j = i`, and otherwise
is exactly the original test at `j`. A right fold therefore eliminates the innermost
binder first while preserving the premises needed for every outer binder.

## Exact prefix endpoint

For every original name list, matrix, and valuation, if the original executable
fragment test succeeds, the concrete output satisfies

`(LinearBlock.eliminate names p).eval nu` iff
`NormalForm.existsPrefix nu names p`.

The induction uses the same updated valuation at each source binder. A repeated
binder name is not silently discarded or renamed; the inner elimination removes
that name's occurrences, and the corresponding outer witness is then vacuous.
The empty prefix returns the original matrix. Exact output support removes precisely
the names in the original list, including all their syntactically retained zero weights.

## Effectivity and scope

The numeric test and compiler are the actual list-all and right-fold programs on
the original radix-six formula codes. Their calibration is unconditional for typed
input syntax; their primitive-recursion proofs apply jointly to the entire original
name list and formula code. No practical output-size or running-time bound is claimed.

This closes a multi-name linear fragment of the Snyatkov/BASE elimination machinery
supporting paper08 `thm:snyatkov`. It does not prove arbitrary nonlinear elimination,
active-hyper case assembly, general anchors, dominant boundaries, exhaustive case
selection, or the unrestricted quantified-block induction. No whole numbered source
statement or separate PA-recursion endpoint is promoted.
