Yes, it is preserved: the literal shift front reaches `AlignedBetaRow.instanceRun` unchanged, with the same `Va` and the same raw program, and the saved scoped lambda beta lemma applies to it. The bridge is a short theorem (below, not compiled; no files written), but it needs five facts that the aligned row does not supply.

## Why the instance survives

The open chain never uses `InstanceFit`; it is universally quantified in `U`. Parameterizing the packet therefore only substitutes a term for `U`. The equalities needed are:

| What must agree | Where | Kind |
| --- | --- | --- |
| Program in `instanceRun` = program in the beta leaf | `exact_OpenAddressedBetaInstance` lines 39 and 44: both are the same variable `U` of `withBetaLeaf V U leaf` | identical variable |
| That `U` = the `U` of the joined outcome | `exact_OpenJoinedBetaOutcome` lines 79, 90, 107, 132 | identical variable |
| `Va` | `unitAuxSyntax V tv` in the packet (line 165) and in the outcome (line 82) | same expression |
| Raw program | The outcome uses `selectedJoinedRaw s base Tg V tv baseM leaf other`. That is an `abbrev` for `guardedRaw (strictDualRaw (measuredStrictCover V tv baseM) s leaf other base base Tg (unitAuxSyntax V tv) Tg)`, which is the packet's raw at `other := lambdaFallback other₀` | reducible unfolding |
| Least program | `leastEq : actualLeast = L := rfl` at outcome line 123 | already compiled |
| `U` after the patch | `U = mk Va`, with `mk` the literal-front constructor; it beta-reduces to the lemma's program at `V := Va` | beta |
| Derivability wrapper | `D` in `…EnrichedEdgeProof` and in `…RootDispatchOpenProof` are both `abbrev … := Nonempty (Derivation B Γ f)` | reducible |

So at the real row, `instanceRun` is `programGraph (zeroDepthInstance (singletonLambda Va (shiftHitLiterals Va H) (singletonBound Va (shiftHitLiterals Va H) U₃))) (suc r) ![a,body]`. That is the `held` premise of `exact_OpenBetaLambdaShiftedBoundLiteralTargetAt`, except that the replacement is the abstract `a` where the lemma wants `boundTerm ty i`.

## Theorem

Suggested path: `LogicLineages/PersistentMarking/NumberedWindowInternalLiteralAlignedBetaShiftedLiteralProof.lean`

```lean
module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBetaOperandAlignmentProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonShiftHitInstallationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAlignedBetaShiftedLiteralProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (headTransport)
open ID1Completion.InternalAdditionLawsProof (add)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D)
open NumberedWindowInternalLiteralBetaLeafOpenProof (rawLambdaTerm)
open NumberedWindowInternalLiteralBetaOperandAlignmentProof (AlignedBetaRow)
open NumberedWindowInternalLiteralSingletonDepthNumericProof (zeroDepthInstance)
open NumberedWindowInternalLiteralSingletonBoundMachineProof (singletonBound)
open NumberedWindowInternalLiteralSingletonBoundOpenRowsProof (boundTerm)
open NumberedWindowInternalLiteralSingletonLambdaMachineProof (singletonLambda)
open NumberedWindowInternalLiteralSingletonShiftHitAtomsMachineProof (shiftHitLiterals)
open NumberedWindowInternalLiteralSingletonShiftHitInstallationProof
  (exact_OpenBetaLambdaShiftedBoundLiteralTargetAt)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- At an aligned beta row whose instance is the literal-front lambda
program over the syntax program `V`: a bound-literal replacement
discharged into a lambda over the discharged index gives the row's own
target, raised by the binder depth one. The row supplies only the
instance run; the two shapes and the three syntax hits are premises. -/
theorem exact_AlignedBetaRowShiftedBoundLiteral (V : Program 1) (H : Program 2) (U₃ : Program 3)
    (L₀ L : Program 3)
    (ctx dom cod fn arg sc st after q r d e f a bind body y ty i lamTy t : OTerm α)
    (row : AlignedBetaRow L₀ L
      (zeroDepthInstance (singletonLambda V (shiftHitLiterals V H)
        (singletonBound V (shiftHitLiterals V H) U₃)))
      B Γ ctx dom cod fn arg sc st after q r d e f a bind body y)
    (replacement : D B Γ (eqn a (boundTerm ty i)))
    (shape : D B Γ (eqn body (rawLambdaTerm lamTy (boundTerm t (suc z)))))
    (inserted : D B Γ (unary V (suc z) (boundTerm ty i)))
    (outerNode : D B Γ (unary V (suc z) (rawLambdaTerm lamTy (boundTerm t (suc z)))))
    (innerNode : D B Γ (unary V (suc z) (boundTerm t (suc z)))) :
    D B Γ (eqn (suc r) (suc (rawLambdaTerm lamTy (boundTerm ty (add i (suc z)))))) :=
  exact_OpenBetaLambdaShiftedBoundLiteralTargetAt V H U₃ ty i body lamTy t r
    inserted outerNode innerNode shape
    (headTransport _ (suc r) a (boundTerm ty i) ![body] replacement row.instanceRun)

#print axioms exact_AlignedBetaRowShiftedBoundLiteral
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAlignedBetaShiftedLiteralProof
```

At the real row, `V` is `unitAuxSyntax V tv`. `H` and `U₃` are the seeds from `exact_SingletonLambdaLiteralsInstanceConstructor`, which is proposed in my last reply and not yet in the saved instance module. The theorem itself holds for any `H` and `U₃`.

## What the row does not supply

`AlignedBetaRow` gives the source equation, `eqn f (rawLambdaTerm bind body)`, the type equations, the two least-class reports, the instance run, and the target class and address. It gives none of the five premises above:

- **`replacement` and `shape`.** These say which case is being treated. They belong to a node-case split on `a` and `body`, not to the row.
- **`inserted`, `outerNode`, `innerNode`.** These are hits of `Va` on the replacement, on the body, and on the node under the binder. The beta leaf checks `Va` only on the whole source `q` and on the target `r`, and `exact_OpenInstalledBetaLeafShape` discards even those two.

So the missing alignment theorem is syntax-hit propagation, in two steps:

1. From `unary Va (suc z) (auxiliaryTerm d e f a)`, derive hits on `f` and on `a`.
2. From `unary Va (suc z) (rawLambdaTerm bind body)`, derive a hit on `body`, and from that on the node under the binder.

A prerequisite is to keep the leaf's `onRaw Va 0` conjunct on `q`. `exact_OpenLiteralBetaCalls` currently extracts only the four later conjuncts of `literalBetaLeaf`.

I found only the introduction direction for auxiliary nodes (`exact_OpenUnitAuxSyntaxIntro`). Four files named `NumberedWindowInternalCoverAuxSyntaxOpen{Intro,IntroRow,Parent,Row}Proof` exist; I did not read them, and the last two may contain the elimination direction.

## Compile risks

- **`headTransport`.** It is stated with `Fin.cons s xs`; here the input is `![a,body]` with `xs := ![body]`. The existing use in `…LambdaPrefixReportsProof` is for a one-input program, so this is its first two-input use.
- **Imports.** The new module imports the old alignment chain together with the shift-hit installation chain. I did not check that pairing for a clash.
