Neither guard follows from the row. The body guard needs a descent through the redex's lambda node, and the installed `Va` cannot be opened there. One level of descent (through the auxiliary node, in the same `Va`) does follow from existing lemmas; the theorem is below, uncompiled, and I wrote no files.

I picked the lambda-node guard: `unary Va (suc z) body`, where the row has `eqn q (auxiliaryTerm d e f a)` and `eqn f (rawLambdaTerm bind body)`.

## Where the derivation stops

1. **The row has no `Va` hit to start from.** `literalBetaLeaf V U` begins with the conjuncts `onRaw V 0` and `onRaw V 2`, which are hits on `q` and `r`. `exact_OpenLiteralBetaCalls` (`…BetaLeafOpenProof`, lines 57–63) returns only the four later conjuncts. So `BetaCalls`, `exact_OpenInstalledBetaLeafShape`, `exact_OpenAddressedBetaInstance` and `AlignedBetaRow` never carry the hit.
2. **From a hit on `q`, the auxiliary node opens.** `exact_OpenCoverAuxSyntaxParent` turns a hit of `auxSyntax V T` on `auxiliaryTerm dom cod fn arg` into hits on `fn` and `arg`. With `normalizeRecover` and `normalizeAccept` this lifts to `Va`. That reaches the redex lambda `f` and the replacement `a`.
3. **The lambda node does not open.** `auxSyntaxUpdate V T := branch certain (unaryAfter V currentKey) (auxAccept T)` runs the supplied `V` on every non-auxiliary row. The packet's `V` is the witness of `ExactSelectedFactoredCover` (`∃ V M G, TermSyntaxCalibrated V ∧ …`), which is a numeric contract only. No object-level law says anything about that `V` on `rawLambdaTerm bind body`.

The bound-node guard fails at the same place: introducing a hit on `boundTerm t i` also needs `V` open at a non-auxiliary tag.

## The part that follows

This is the converse of the existing `exact_OpenUnitAuxSyntaxIntro`, for the same `V`, `TV`, `B`, `Γ` and inputs.

Suggested path: `LogicLineages/PersistentMarking/NumberedWindowInternalLiteralNormalizedAuxSyntaxPartsProof.lean`

```lean
module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralNormalizedAuxSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxSyntaxOpenParentProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceNormalizationProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralNormalizedAuxSyntaxPartsProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceNormalizationProof (normalizeAccept normalizeRecover)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalCoverAuxSyntaxTargets (auxSyntax)
open NumberedWindowInternalCoverAuxSyntaxOpenParentProof (exact_OpenCoverAuxSyntaxParent)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalLiteralNormalizedAuxSyntaxProof (unitAuxSyntax)

/-- A unit syntax hit on a literal auxiliary parent gives the same unit
hit on its function and argument. Same program, same context. -/
theorem exact_OpenUnitAuxSyntaxParts (V TV : Program 1) (B : Positive (Fin 1)) (α : Type)
    (Γ : List (Formula α)) (dom cod fn arg : OTerm α)
    (parent : Nonempty (Derivation B Γ
      (unary (unitAuxSyntax V TV) (suc z) (auxiliaryTerm dom cod fn arg)))) :
    Nonempty (Derivation B Γ (unary (unitAuxSyntax V TV) (suc z) fn)) ∧
    Nonempty (Derivation B Γ (unary (unitAuxSyntax V TV) (suc z) arg)) := by
  have raw := normalizeRecover (auxSyntax V TV) ![auxiliaryTerm dom cod fn arg] parent
  obtain ⟨children⟩ := exact_OpenCoverAuxSyntaxParent V TV B α Γ dom cod fn arg raw
  have parts : Derivation B Γ
      (unary (auxSyntax V TV) (suc z) fn ⊓ unary (auxSyntax V TV) (suc z) arg) :=
    Derivation.conjunctionRight children
  exact ⟨normalizeAccept (auxSyntax V TV) ![fn] ⟨Derivation.conjunctionLeft parts⟩,
    normalizeAccept (auxSyntax V TV) ![arg] ⟨Derivation.conjunctionRight parts⟩⟩

#print axioms exact_OpenUnitAuxSyntaxParts
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralNormalizedAuxSyntaxPartsProof
```

Given a hit on `q` and the row's `source` equation, this supplies the hit on `a`. After transport along `replacement` that is the `inserted` guard. It also gives the hit on `f`, which is the input to the missing lambda step.

## The missing bridge, exactly

Two obligations remain for the lambda-node guard:

- **Carry the leaf's source hit.** A lemma from `D B Γ (bit (literalBetaLeaf V U) ![q,w,r])` to `D B Γ (unary V (suc z) q)`, then threaded through the three continuation theorems named in step 1, or added as a field of `AlignedBetaRow`. The fact is physically in the leaf; only the plumbing is absent.
- **Lambda descent for the installed program.** At `Va := unitAuxSyntax V tv`, with the packet's `V`:

  ```lean
  ∀ (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ty b : OTerm α),
    D B Γ (unary Va (suc z) (rawLambdaTerm ty b)) → D B Γ (unary Va (suc z) b)
  ```

  This is unprovable for the current `V`. It needs the packet to select a `V` with a literal lambda row whose child bit is the program's own, with a parent-form open theorem like the auxiliary one.

What exists towards the second obligation is `lambdaSyntax V T` in `NumberedWindowInternalCoverLambdaSyntaxRowTargets`, with the open-row target `ExactOpenCoverLambdaSyntaxRow`. It does not close the gap as it stands:

- its target is row-level only, with no parent form like `ExactOpenCoverAuxSyntaxParent`;
- the child bit it recovers is for `lambdaSyntax V T`, not for the program that later wraps it;
- the packet does not install it.

## Not checked

- I did not read `NumberedWindowInternalCoverLambdaSyntaxRowOpenProof`, so I do not know whether the row target is proved.
- A typed-window route might avoid syntax descent. The covered half of the joined window is `coveredMemoWindow … (unitAuxSyntax V TV)`, and `…CoveredMemoAuxRowProof:128` pairs a window graph with a syntax hit on its seed, so a window report at `body` could yield the guard. The row has no window at `body`, and I did not verify a lemma extracting the hit.

## Compile risks

- `parts` relies on `auxSyntaxChildren` unfolding to its two-level conjunction.
- `exact_OpenCoverAuxSyntaxParent` lives in a `public section` module without `@[expose]`. That is fine for using the theorem, but I import it privately and did not check the pairing with the normalized-syntax module.
