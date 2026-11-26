# Exact extra-compression scope and proof plan

Source: Paper16 `sections/composition.tex`, `lem:extra-compression`, lines 251–269. Target: `ExtraCompressionTargets.ExtraCompression`.

Mapping: `P` and `T` are the literal typed, valid marked owners at the same output type. `Equivalent S f g` is the printed fixed head-class equivalence. `ExtendedMatchingTree` is the actual occurrence matching of the original base lists. `ExtendedWholeTree S f base extras targetExtras` supplies, in target occurrence order, exactly the asserted auxiliary weak comparison from the original whole owner retyped to each target extra's type. Its recursive data representation does not change the number or order of premises. The existential wrapper requires no computable extraction of arbitrary Prop proofs.

Construct a list `p` containing a complete original source owner retyped once per target-extra occurrence. Its annotations are derived from the actual target extras. Simultaneously transform the Whole witness to an actual ordered comparison from `p` to target extras. Prove all intermediate owner terms typed and valid using the original owner facts and each target extra's typing; no caller-supplied output-validity premise.

Use literal In at source `(base;p)` against target `(targetBase;targetExtras)`, then Drop to source `(base;p ++ extras)`, then Perm to source `(base;extras ++ p)`, then Copies to source `(base;extras)`. Prove the exact positional append-block permutation via actual Remove/Permutation witnesses. Every entry of `p` is a full-prefix copy of the original owner, not a copy of a modified owner. There is no comparison composition, cut, arbitrary-target admissibility, or general application associativity premise.

This is the whole printed extra-compression lemma, not one ordinary-target instance. The following unrestricted-target sharp-admissibility packet must retain all five families and separately handle In, Marked1 and Marked2; their premises cannot be discharged by ordinary-target contradictions.

Freeze before proof; independent scope review then native gate and final evidence are required.
