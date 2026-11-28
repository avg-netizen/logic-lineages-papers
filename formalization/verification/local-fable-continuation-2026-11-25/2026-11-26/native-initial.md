The open raw-step-preservation premise is not a named declaration anywhere in the tree. It sits inside the `beta` hypothesis of `exact_OpenApplicationComputabilityFromBeta`. The saved beta consumer does not yet apply to the installed window, because the window installs a different instance program. Nothing below is compiled.

## Trace

**Milestone.** `TypedCarrierComputability` (`Paper16AccessibilityMilestoneTargets.lean:111`) has no separate lambda field; the lambda case is inside it.

**Source level.**
- `ComputableLambda` and the reduct split `AppliedLambdaReducts` are at `NumberedWindowExternalLambdaComputabilityTargets.lean:28` and `:19`. The split has four alternatives: bottom, bottom function, body step, instance.
- The body-step alternative is where preservation enters. `SubstitutionWindowStep` (`NumberedWindowExternalWindowSubstitutionTargets.lean:16`) says a typed raw step stays a typed raw step under substitution, or both images are equal and a bottom was substituted.
- It is proved as `exact_SubstitutionWindowStep` and used by `edgeOrEqual` and `freePositive` in `NumberedWindowExternalInstancePathProof.lean:13,36`. I read those two only as grep hits, not in full.

**Arithmetic, closed numeric.**
- `exact_CheckedSingletonRawPreservation` and `exact_CheckedFreshOpening` (`…SingletonRawPreservationProof.lean:36,59`) are stated with `evaluate` on `encodeTerm` codes of closed `NTerm`s.
- They need `uFit : DepthInstanceFit U` and `pFit : ActualRawCalibration …`. Its docstring says it is "not yet an open-arithmetic proof of naturality".

**Arithmetic, open fields.**
- `exact_OpenApplicationComputabilityFromBeta` (`…BetaApplicationComputabilityProof.lean:46`) takes the hypothesis `beta`. It is a `BetaOutcomeAt … (formula p τ y)` for every direct reduct `y`.
- `BetaOutcomeAt` (`…JoinedBetaOutcomeProof.lean:66`) hands its continuation an `AlignedBetaRow` (`…BetaOperandAlignmentProof.lean:32`). The relevant fields are `functionShape`, `instanceRun : programGraph U (suc r) ![a,body]`, `targetClass` and `targetAddress`.
- What is already proved around it is `BetaApplicationCases`, packaged as `BetaJoinedRulesAt.betaCases` by `exact_ConcreteLambdaJoinedRules`. That theorem's docstring says "This is not yet full lambda closure".
- For the body-step side, `exact_OpenScopedLambdaRawCases` (`…LambdaScopedRawCasesProof.lean:58`) delivers an open body step at the pushed context. No declaration carries that step to a step between the two instances.

## Smallest boundary reachable from the installed child computation

`AlignedBetaRow.instanceRun` has exactly the type of the `held` premise of the saved `exact_OpenBetaLambdaBoundAboveTarget`. So inside one `BetaOutcomeAt` continuation, with the body derivably a lambda over a bound variable above depth one, the target `r` is identified with open fields. That is the image half of raw preservation (the first two conjuncts of `exact_CheckedSingletonRawPreservation`) for this node shape.

Three things stand between that and the goal `formula p τ y`:

- **Program mismatch.** Both packets choose the instance program by `obtain ⟨U,uFit⟩ := exact_LiteralSingletonInstance` (`…BetaJoinedMemoPacketProof.lean:186`, `…LambdaJoinedMemoPacketProof.lean:191`). That `U` is an abstract program with only `InstanceFit U`. The saved theorems are about the physical `zeroDepthInstance (singletonLambda V H (singletonBound V H W))`. A closed numeric fit cannot move an open derivation from one program's graph to another's.
- **Guards.** The leaf checks its syntax program on tape slots 0 and 2 (`literalBetaLeaf`, `…BetaLeafProof.lean:59`). `inserted`, `lambdaNode` and `boundNode` are not supplied by the row and stay premises, as does `shape`.
- **The step half.** No open-field version of `exact_CheckedSingletonRawPreservation` exists. The numeric one cannot be lifted, since it speaks about `evaluate` at codes, not about derivations.

## Unproved premise

On the installation path it is `slotFit : GuardedDepthInstanceFit (singletonLambdaDispatch W)`, the hypothesis of `exact_LiteralSingletonLambdaCalibrationOfGuarded` (`…GuardedCalibrationProof.lean:68`). Even with it, the two packet theorems would have to take `U` and its fit as parameters. I did not read their full proofs to see whether anything else about `U` is used.

## Bridge (closed numeric)

This discharges the existing hypotheses `InstanceFit` and `LeafFit` at the physical lambda program. It is `exact_PhysicalSingletonBetaInstallation` with the guarded lambda calibration substituted for the bound calibration.

Suggested file: `LogicLineages/PersistentMarking/NumberedWindowInternalLiteralSingletonLambdaBetaInstallationProof.lean`

```lean
module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonBetaInstallationProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonGuardedCalibrationProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonLambdaBetaInstallationProof

open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowRootDispatchAlgorithm (fixed)
open NumberedWindowInternalSparseTypedRawTargets (ActualRawSyntax)
open NumberedWindowInternalLiteralRootDispatchNumericProof (LeafFit)
open NumberedWindowInternalLiteralBetaLeafProof (InstanceFit withBetaLeaf)
open NumberedWindowInternalLiteralBetaLeafNumericProof (exact_LiteralBetaLeafFit)
open NumberedWindowInternalLiteralSingletonDepthNumericProof (zeroDepthInstance exact_ZeroDepthInstance)
open NumberedWindowInternalLiteralSingletonBoundMachineProof (ShiftHitFit)
open NumberedWindowInternalLiteralSingletonLambdaMachineProof (singletonLambda singletonLambdaDispatch)
open NumberedWindowInternalLiteralSingletonGuardedCalibrationProof
  (GuardedDepthInstanceFit exact_LiteralSingletonLambdaCalibrationOfGuarded)

/-- Numeric installation of the physical lambda instance at the beta leaf.
The only premise beyond the original syntax and shift fits is the guarded
fit of the written lambda dispatch slot. This is a statement about
evaluation on numerals, not an open derivation. -/
theorem exact_PhysicalSingletonLambdaBetaInstallation (xs : Entries) (heads : List Nat)
    (V : Program 1) (H : Program 2) (W : Program 3) (leaf : Nat → Program 3)
    (vFit : ActualRawSyntax V) (hFit : ShiftHitFit H)
    (slotFit : GuardedDepthInstanceFit (singletonLambdaDispatch W))
    (fit : LeafFit (fixed xs heads) leaf) :
    let betaInstance := zeroDepthInstance (singletonLambda V H W)
    InstanceFit betaInstance ∧ LeafFit (fixed xs heads) (withBetaLeaf V betaInstance leaf) := by
  have instanceFit := exact_ZeroDepthInstance (singletonLambda V H W)
    (exact_LiteralSingletonLambdaCalibrationOfGuarded V H W vFit hFit slotFit)
  exact ⟨instanceFit, exact_LiteralBetaLeafFit xs heads V _ vFit instanceFit leaf fit⟩

#print axioms exact_PhysicalSingletonLambdaBetaInstallation
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonLambdaBetaInstallationProof
```

## Closed numeric versus open

| Closed numeric (evaluation on numerals) | Derivation with open fields |
|---|---|
| `InstanceFit`, `DepthInstanceFit`, `GuardedDepthInstanceFit` | `BetaOutcomeAt`, `AlignedBetaRow` |
| `exact_CheckedSingletonRawPreservation`, `exact_CheckedFreshOpening` | `exact_OpenScopedLambdaRawCases` |
| `InstanceFit U` in `exact_ConcreteLambdaJoinedRules` | `BetaJoinedRulesAt.betaCases` |
| the bridge above | the saved `…BoundAbove…` theorems |

I worked from the Lean tree only; the manuscript section is outside this directory.
