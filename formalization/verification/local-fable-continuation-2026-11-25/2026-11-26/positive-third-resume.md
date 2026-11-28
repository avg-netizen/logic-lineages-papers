Of the five residual facts, only one (`inserted`) has an existing derivation, and it needs a fact the aligned row drops. The first genuinely missing relation is syntax descent through a lambda node for the installed syntax program. A small supplier for the derivable part is below; nothing is compiled or written.

## What the trace shows

- **The leaf does check syntax, on the redex and the target.** `literalBetaLeaf V U` begins with `onRaw V 0` and `onRaw V 2`, i.e. `V` on `q` and on `r`. `exact_OpenLiteralBetaCalls` discards both conjuncts, so `BetaCalls`, `exact_OpenAddressedBetaInstance`, `AlignedBetaRow` and `BetaOutcomeAt` carry no `unary V …` fact at all.
- **In the joined installation the leaf's `V` is `unitAuxSyntax V tv`**, which is `normalize (auxSyntax V tv)`. `auxSyntaxUpdate` is physical only on tag-6 rows; on every other key, including lambda nodes, it runs the opaque `V`.
- **Auxiliary descent exists:** `exact_OpenCoverAuxSyntaxParent` turns acceptance of `auxiliaryTerm dom cod fn arg` into acceptance of `fn` and `arg`.
- **Lambda descent does not exist for the installed program.** A physical lambda row exists only for `lambdaSyntax V T`, at table-row level (`exact_OpenCoverLambdaSyntaxRow`), and `lambdaSyntax` is not referenced by any `NumberedWindowInternalLiteral*` module.
- **`exact_OpenScopedLambdaRawCases`** supplies window membership of the child source and target in the pushed context (`windowAt Q (rawCons d c) cod a`) and the child raw step. It gives neither a `unary V` fact nor a body shape for the beta redex. I did not trace whether the covered half of that window implies the syntax bit.

## Status of the five facts

| Residual fact | Status |
|---|---|
| `U` is `zeroDepthInstance (singletonLambda V H (singletonBound V H W))`, same `V` as the leaf | a choice at installation, no derivation needed |
| `inserted : unary V (suc z) a` | derivable from the leaf's first conjunct and `row.source` (supplier below) |
| `lambdaNode : unary V (suc z) (λ lamTy. bound t 1)` | **missing**: needs `V (λ bind. body) → V body` |
| `boundNode : unary V (suc z) (bound t 1)` | missing: the same descent once more |
| `shape : body = λ lamTy. bound t 1` | a case hypothesis of the caller's split on `body`, not a derivable fact |

## Supplier

`LogicLineages/PersistentMarking/NumberedWindowInternalLiteralBetaLeafSyntaxSupplierProof.lean`

```lean
module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBetaLeafOpenProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralNormalizedAuxSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxSyntaxOpenParentProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceNormalizationProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBetaLeafSyntaxSupplierProof

open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (projectionValue headTransport)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open ID1Completion.InternalAcceptanceNormalizationProof (normalizeAccept normalizeRecover)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary)
open NumberedWindowInternalSparseRawFunctionFrame (onRaw)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalCoverAuxSyntaxTargets (auxSyntax)
open NumberedWindowInternalCoverAuxSyntaxOpenParentProof (exact_OpenCoverAuxSyntaxParent)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D bit)
open NumberedWindowInternalLiteralBetaLeafProof (literalBetaLeaf)
open NumberedWindowInternalLiteralBetaLeafOpenProof (rawLambdaTerm)
open NumberedWindowInternalLiteralNormalizedAuxSyntaxProof (unitAuxSyntax)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- The two syntax conjuncts of an accepted beta leaf, which the beta
call record does not retain: the leaf's own syntax program accepts the
source redex and the target. -/
theorem exact_OpenLiteralBetaLeafSyntax (V : Program 1) (U : Program 2) (q w r : OTerm α)
    (held : D B Γ (bit (literalBetaLeaf V U) ![q,w,r])) :
    D B Γ (unary V (suc z) q) ∧ D B Γ (unary V (suc z) r) := by
  unfold literalBetaLeaf at held
  let xs : Fin 3 → OTerm α := ![q,w,r]
  obtain ⟨a⟩ := conjunctionRecover _ _ xs held
  obtain ⟨b⟩ := conjunctionRecover _ _ xs ⟨Derivation.conjunctionRight a⟩
  have source : D B Γ (unary V (suc z) q) := by
    apply compositionRecover V (fun _ : Fin 1 => .projection (0 : Fin 3)) (suc z) xs ![q]
      ⟨Derivation.conjunctionLeft a⟩
    intro i
    obtain rfl := Fin.eq_zero i
    exact projectionValue (0 : Fin 3) xs
  have target : D B Γ (unary V (suc z) r) := by
    apply compositionRecover V (fun _ : Fin 1 => .projection (2 : Fin 3)) (suc z) xs ![r]
      ⟨Derivation.conjunctionLeft b⟩
    intro i
    obtain rfl := Fin.eq_zero i
    exact projectionValue (2 : Fin 3) xs
  exact ⟨source,target⟩

/-- Auxiliary descent for the installed unit syntax program: acceptance
of a code that is derivably a literal auxiliary application gives both
type bits and the same program's acceptance of the function and the
argument. This is the existing parent theorem between the two
normalization steps. -/
theorem exact_OpenUnitAuxSyntaxOperands (V TV : Program 1) (q dom cod fn arg : OTerm α)
    (source : D B Γ (eqn q (auxiliaryTerm dom cod fn arg)))
    (valid : D B Γ (unary (unitAuxSyntax V TV) (suc z) q)) :
    D B Γ (unary TV (suc z) dom) ∧ D B Γ (unary TV (suc z) cod) ∧
    D B Γ (unary (unitAuxSyntax V TV) (suc z) fn) ∧
    D B Γ (unary (unitAuxSyntax V TV) (suc z) arg) := by
  have moved : D B Γ (unary (unitAuxSyntax V TV) (suc z) (auxiliaryTerm dom cod fn arg)) :=
    headTransport (unitAuxSyntax V TV) (suc z) q (auxiliaryTerm dom cod fn arg) Fin.elim0
      source valid
  have raw := normalizeRecover (auxSyntax V TV) ![auxiliaryTerm dom cod fn arg] moved
  obtain ⟨children⟩ := exact_OpenCoverAuxSyntaxParent V TV B α Γ dom cod fn arg raw
  have types := Derivation.conjunctionLeft children
  have terms := Derivation.conjunctionRight children
  exact ⟨⟨Derivation.conjunctionLeft types⟩,⟨Derivation.conjunctionRight types⟩,
    normalizeAccept (auxSyntax V TV) ![fn] ⟨Derivation.conjunctionLeft terms⟩,
    normalizeAccept (auxSyntax V TV) ![arg] ⟨Derivation.conjunctionRight terms⟩⟩

/-- Supplier for the `inserted` premise. With the leaf graph and the two
row equations `source` and `functionShape`, the installed syntax program
accepts the beta argument, the literal function lambda node, and the
target. Nothing is concluded about the lambda's body. -/
theorem exact_OpenBetaLeafArgumentSyntax (V TV : Program 1) (U : Program 2)
    (q w r dom cod fn arg bind body : OTerm α)
    (leaf : D B Γ (bit (literalBetaLeaf (unitAuxSyntax V TV) U) ![q,w,r]))
    (source : D B Γ (eqn q (auxiliaryTerm dom cod fn arg)))
    (functionShape : D B Γ (eqn fn (rawLambdaTerm bind body))) :
    D B Γ (unary (unitAuxSyntax V TV) (suc z) arg) ∧
    D B Γ (unary (unitAuxSyntax V TV) (suc z) (rawLambdaTerm bind body)) ∧
    D B Γ (unary (unitAuxSyntax V TV) (suc z) r) := by
  obtain ⟨valid,target⟩ := exact_OpenLiteralBetaLeafSyntax (unitAuxSyntax V TV) U q w r leaf
  obtain ⟨_,_,fnValid,argValid⟩ :=
    exact_OpenUnitAuxSyntaxOperands V TV q dom cod fn arg source valid
  exact ⟨argValid,
    headTransport (unitAuxSyntax V TV) (suc z) fn (rawLambdaTerm bind body) Fin.elim0
      functionShape fnValid,
    target⟩

#print axioms exact_OpenLiteralBetaLeafSyntax
#print axioms exact_OpenUnitAuxSyntaxOperands
#print axioms exact_OpenBetaLeafArgumentSyntax
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBetaLeafSyntaxSupplierProof
```

The `source` and `functionShape` hypotheses are exactly `AlignedBetaRow.source` and `AlignedBetaRow.functionShape`. The first conjunct is the saved theorem's `inserted` with `V := unitAuxSyntax V TV`.

## What blocks instantiation

1. **The row lacks the leaf's syntax conjunct.** `exact_OpenBetaLeafArgumentSyntax` needs the leaf graph, which is in scope inside `exact_OpenAddressedBetaInstance` (its `branch` premise, after the tag-6 `conjunctionRecover`) but is not passed on. To use it from `BetaOutcomeAt`, one fact has to be threaded through `exact_OpenLiteralBetaLeafShape`, `exact_OpenAddressedBetaInstance` and `AlignedBetaRow`: `unary V (suc z) q` at the renamed redex. Those are the main thread's checked modules, so I have not drafted that edit.
2. **First genuine missing relation:** for the installed syntax program `Va = unitAuxSyntax V tv`,
   `D B Γ (unary Va (suc z) (rawLambdaTerm bind body)) → D B Γ (unary Va (suc z) body)`.
   It is needed twice (function lambda to `body`, then `body`'s lambda to the bound node). It would need either `V` instantiated with a lambda-aware program plus a parent-level theorem for it (only the row-level `exact_OpenCoverLambdaSyntaxRow` exists), or a different source for the two facts.

**A route that avoids the missing relation, not written.** The three syntax facts look redundant given the held instance graph. `singletonBound` returns zero whenever `singletonSyntax V` rejects (`exact_OpenSingletonBoundGuardZero`), and the held output is `suc r`. The same holds for the child call, whose zero would make the lambda row return zero. What that inversion needs is one lemma I did not find: a successor output of `conjunction p q` forces both conjuncts to accept. It should follow from `zeroBranchElim`, `successorBranchElim` and the `equalsOne` graph characterization behind `equalsOneAcceptInput`. If it holds, `inserted`, `lambdaNode` and `boundNode` all drop out of the saved theorem's hypotheses, leaving only `shape`.

**Unverified points:**
- `headTransport … Fin.elim0` on a one-slot tape must match `unary`'s `![_]` form, as it does in the `predOne` precedent.
- `Derivation.conjunctionLeft children` relies on `auxSyntaxChildren` unfolding to a conjunction, as in the intro-row precedent.
