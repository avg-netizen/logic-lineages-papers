# First-order reduction for certified common-head comparisons

Paper08 `thm:common` (paper.tex lines870–875) gives effective BASE comparison
formulas and then states decidability for arbitrary Boolean and quantified
combinations of certified comparisons. This package proves the intervening
first-order translation, not the missing unrestricted BASE decision supplier.
No whole-statement promotion is made.

Each comparison atom stores its own `List NONote` head certificate and both
`CommonSyntax heads.length` operands. Different atoms may use different heads,
depths and expressions. The only semantic certification premise is the original
`genuineHeads` condition at every atom. It is not an assumed decision procedure
and is not used by the raw-code translator.

Paper08 defines raw variables as positive (introductory convention and A_0 at
lines858–861). Positive existential quantification is therefore represented
explicitly and translated to ordinary Nat existence with 0<x inside the binder.
Nat quantification is separately available, matching the BASE theory's Nat
universe. Universal versions are the literal negation/existential duals. Neither
domain is silently substituted for the other. Repeated binder names use exact
Function.update shadowing. Boolean structure and arbitrary alternation remain
in place; there is no claimed quantifier elimination.

The accepted exact-support atom compiler is translated into the existing
SourceFormula syntax. The whole translation has exact truth, exact free-variable
membership, literal output-code calibration and actual total numeric computation.
Raw malformed atom payloads use an explicit empty-head/zero default; correctness
for genuine source inputs follows calibration of the unchanged typed encoding.
No extra semantic predicate, head-value oracle, fresh variable or free positivity
guard is added. The full thm:common decidability claim remains pending.
