This request matches the previous turn's, and the answer is unchanged: yes, the existing beta consumer can take an existential successor witness. The lemma I gave is already saved, byte-for-byte as I wrote it, in `LogicLineages/PersistentMarking/NumberedWindowInternalLiteralSingletonLambdaBoundHitBetaProof.lean`. It is still uncompiled; this turn I re-read it against the source signatures.

## The lemma

```lean
theorem exact_OpenBetaLambdaBoundHitTarget (V : Program 1) (H : Program 2) (W : Program 3)
    (a body lamTy t r : OTerm α) (goal : Formula α)
    (inserted : D B Γ (unary V (suc z) a))
    (lambdaNode : D B Γ (unary V (suc z) (rawLambdaTerm lamTy (boundTerm t (suc z)))))
    (boundNode : D B Γ (unary V (suc z) (boundTerm t (suc z))))
    (shape : D B Γ (eqn body (rawLambdaTerm lamTy (boundTerm t (suc z)))))
    (held : D B Γ (programGraph (zeroDepthInstance (singletonLambda V H (singletonBound V H W)))
      (suc r) ![a,body]))
    (use : ∀ (β : Type) (ρ : α → β) (Δ : List (Formula β)) (u : OTerm β),
      (∀ f ∈ Γ, f.relabel ρ ∈ Δ) →
      D B Δ (programGraph H (suc u) ![a.relabel ρ,suc z]) →
      D B Δ (eqn (suc (r.relabel ρ)) (suc (rawLambdaTerm (lamTy.relabel ρ) u))) →
      D B Δ (goal.relabel ρ)) : D B Γ goal
```

`exact_OpenAlignedBetaLambdaBoundHit` in the same file is this with `held := row.instanceRun` from an `AlignedBetaRow`. Both end with `#print axioms`.

## Why the existential witness is enough

- `optionGraphCases H ![a, suc z]` is `programCases` followed by the zero/successor split; it supplies either output `z` or output `suc u` in an extended context.
- In the zero branch the instance would return `z` (`exact_OpenSingletonBoundAtPositiveDepth`, then `exact_OpenSingletonLambdaRowZero`, then `exact_OpenZeroDepthInstance`). `valueUnique` against the held `suc r` gives `suc r = z`, which `sucNeZeroApply` refutes. So `H` never has to be shown nonzero.
- In the successor branch `exact_OpenBetaLambdaBody` gives the rebuilt node around `u`, and `valueUnique` gives the target equation.

## Same-program requirement, equality, numeric fit

- **Same program:** the `H` in the witness graph is the `H` inside the installed instance, with no condition on it. A cutoff-general three-slot program is not needed by this consumer.
- **Equality to the true substituted body:** not delivered and not needed here. The witness `u` is tied to the replacement only through `programGraph H (suc u) ![a, suc z]`. When the replacement has a physical row (bound, free, bottom), one `valueUnique` on `H` against the saved literal hit turns that into a term equation. For an opaque shape no such term exists.
- **Numeric fit:** not used by this consumer, and it would not produce the missing equation either. It matters only if a later step needs a property of `u` itself, such as the raw-preservation premise on `r` in checkpoint 4; I have not traced that step.

## Re-read against sources this turn

- `optionGraphCases`: argument order, branch binder order, and the form `fun i => (xs i).relabel j` all match the proof's `intro` lines and the `binaryInputsRename` rewrite.
- `sucRelabel`, `zRelabel`, `renameInto`, `sucNeZeroApply`: signatures match their uses.
- Argument orders of `exact_OpenSingletonBoundAtPositiveDepth`, `exact_OpenSingletonLambdaRowZero`, `exact_OpenBetaLambdaBody`, `exact_OpenZeroDepthInstance` and `AlignedBetaRow`: all match.

I found no definite error. The one fragile spot remains the four `rw` chains that move premises into the extended context: each needs a second `sucRelabel, zRelabel` for the literal `suc z` index, and the rewrites depend on instance order.
