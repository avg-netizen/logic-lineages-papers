# Independent final review: paper19 cor:ground-equivalence (root, local continuation)

Accepted as the current numbered statement `cor:ground-equivalence`
(compiler.tex 175–178). Reviewer: root of the local three-party continuation,
not the lane B author. No reviewer native run.

Comparator `CurrentGroundEquivalenceTargets.Complete` = Effective ∧
ExactReductions. For every n and every pair of actual ground-output typed
inputs over n ground free variables: the two counterexample formulas and the
two reductions are computed on raw codes by Computable routines and equal the
literal encodings of the typed constructions; for every control with the
printed source growth and every policy, the weak query holds iff the compiled
strict comparison holds, and the strict query holds iff the compiled weak
comparison holds (the two many-one directions); both output contexts are
all-ground; and the four output table lengths are at most
60000*(max(|a|,|b|)+1)+7, a linear and hence polynomial DAG bound. No
recognition of an arithmetic fragment, decider or witness premise is added.

Seven frozen pins recomputed and match. Compiler-free recursive evidence
reproduced independently and JSON-identical to the author's file: 463
source-matched modules, zero errors; the exact alias and all other audited
declarations depend only on propext, Classical.choice and Quot.sound. Gate
receipt 1795036028399836249-12. No unsafe, opaque, implemented_by, extern,
partial, axiom, sorry or native_decide in the ControlSensitivityCurrent files
of the closure. It rests on `thm:compiler` (packet 392).

`thm:control-hardness` and the later paper19 statements remain pending. No
full-root or CI claim.
