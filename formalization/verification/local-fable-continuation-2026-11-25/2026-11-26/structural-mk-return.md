Yes: the constructor can be built from saved results alone, with no hypothesis left over. For the program as defined last turn, `H` and `U` and their fits are chosen before the syntax program, so nothing but the syntax fit depends on `Va`. Nothing below has been compiled; I wrote no files.

One caveat first: neither the `mk`/`mkFit` packet factoring nor `singletonLambdaInstanceOf` is in the worktree yet. The lemmas below are therefore stated with the constructor written out, and depend only on saved modules.

## Which hypotheses depend on `Va`

| Hypothesis | Mentions the syntax program? | How it is supplied |
| --- | --- | --- |
| `ActualRawSyntax Vs` | Yes — it is the fit of `Vs` itself | The packet's `rawSyntaxFit` (line 213), handed to `mkFit` at `Vs := Va` |
| `ShiftHitFit H` | No — `∀ a d, evaluate H … = shiftHitValue a d` | `exact_LiteralShiftHit` |
| `GuardedDepthInstanceFit U` | No — it refers to the algorithm `syntaxBits`, not to any program | `exact_LiteralDepthInstance`, then `exact_GuardedOfDepthInstanceFit` |
| `LambdaChildFit U` | No | Already derived by `exact_LambdaChildFitOfGuarded`; not a hypothesis of the calibration used here |

So `H` and `U` can be fixed once, outside the packet, and the only thing the packet must hand over is the fit of its own `Va`.

There is one variant where a dependence does appear. The other lane's installed rows (`NumberedWindowInternalLiteralSingletonShiftHitInstallationProof`) use `singletonLambda V (shiftHitLiterals V H) (singletonBound V (shiftHitLiterals V H) U)`. There the shift slot and the fallback slot are built from `V`, so their fits depend on `Va`. They depend on it only through `ActualRawSyntax Vs`, which `mkFit` already receives, so no new witness is needed. The second lemma below covers that case; it also discharges the `slotFit` premise that `exact_PhysicalSingletonLambdaLiteralsInstallation` currently leaves explicit.

## Lemmas

Suggested path: `LogicLineages/PersistentMarking/NumberedWindowInternalLiteralSingletonLambdaInstanceProof.lean`

```lean
module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonLambdaChildFitProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonShiftHitAtomsMachineProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonLambdaInstanceProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparseTypedRawTargets (ActualRawSyntax)
open NumberedWindowInternalLiteralBetaLeafProof (InstanceFit)
open NumberedWindowInternalLiteralSingletonDepthNumericProof
  (DepthInstanceFit zeroDepthInstance exact_ZeroDepthInstance exact_LiteralDepthInstance)
open NumberedWindowInternalLiteralSingletonBoundMachineProof
  (ShiftHitFit singletonBound exact_LiteralShiftHit)
open NumberedWindowInternalLiteralSingletonGuardedCalibrationProof
  (GuardedDepthInstanceFit exact_GuardedOfDepthInstanceFit
    exact_LiteralSingletonBoundGuardedCalibration)
open NumberedWindowInternalLiteralSingletonLambdaMachineProof (singletonLambda)
open NumberedWindowInternalLiteralSingletonLambdaChildFitProof
  (exact_LiteralSingletonLambdaCalibrationOfFallback)
open NumberedWindowInternalLiteralSingletonShiftHitAtomsMachineProof
  (shiftHitLiterals exact_ShiftHitLiteralsFit)

/-- The shift and fallback programs are chosen before the syntax program.
For every calibrated syntax program the written lambda instance over
them is calibrated at all depths, and its depth-zero wrapper is a beta
instance. No hypothesis remains. -/
theorem exact_SingletonLambdaInstanceConstructor :
    ∃ (H : Program 2) (U : Program 3), ShiftHitFit H ∧ DepthInstanceFit U ∧
      ∀ Vs : Program 1, ActualRawSyntax Vs →
        DepthInstanceFit (singletonLambda Vs H U) ∧
        InstanceFit (zeroDepthInstance (singletonLambda Vs H U)) := by
  obtain ⟨H,hFit⟩ := exact_LiteralShiftHit
  obtain ⟨U,uFit⟩ := exact_LiteralDepthInstance
  refine ⟨H,U,hFit,uFit,fun Vs vFit => ?_⟩
  have fit := exact_LiteralSingletonLambdaCalibrationOfFallback Vs H U vFit hFit
    (exact_GuardedOfDepthInstanceFit U uFit)
  exact ⟨fit,exact_ZeroDepthInstance (singletonLambda Vs H U) fit⟩

/-- The same program with the physical shift front and the physical
atom and bound fallback. Both slots are built from the syntax program;
their fits follow from the one syntax fit. -/
theorem exact_SingletonLambdaLiteralsInstanceFit (H : Program 2) (U : Program 3)
    (hFit : ShiftHitFit H) (uFit : GuardedDepthInstanceFit U)
    (Vs : Program 1) (vFit : ActualRawSyntax Vs) :
    InstanceFit (zeroDepthInstance (singletonLambda Vs (shiftHitLiterals Vs H)
      (singletonBound Vs (shiftHitLiterals Vs H) U))) := by
  have shiftFit := exact_ShiftHitLiteralsFit Vs H vFit hFit
  have slotFit : GuardedDepthInstanceFit (singletonBound Vs (shiftHitLiterals Vs H) U) :=
    exact_GuardedOfDepthInstanceFit _
      (exact_LiteralSingletonBoundGuardedCalibration Vs (shiftHitLiterals Vs H) U vFit shiftFit uFit)
  exact exact_ZeroDepthInstance _
    (exact_LiteralSingletonLambdaCalibrationOfFallback Vs (shiftHitLiterals Vs H)
      (singletonBound Vs (shiftHitLiterals Vs H) U) vFit shiftFit slotFit)

#print axioms exact_SingletonLambdaInstanceConstructor
#print axioms exact_SingletonLambdaLiteralsInstanceFit
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonLambdaInstanceProof
```

## How this feeds `mk`/`mkFit`

From the first lemma, after `obtain ⟨H,U,hFit,uFit,build⟩`, the two packet arguments are:

```lean
(fun Vs => zeroDepthInstance (singletonLambda Vs H U))
(fun Vs vFit => (build Vs vFit).2)
```

`(build Va vFit).1` is the all-depth fit of the installed inner program, available because the factored packet exports `ActualRawSyntax Va`.

For the physical-front variant, the arguments are the constructor in the second lemma's statement and `exact_SingletonLambdaLiteralsInstanceFit H U hFit (exact_GuardedOfDepthInstanceFit U uFit)`.

## What is and is not missing

- **No missing witness** for either constructor: every fit is supplied by a saved theorem.
- **Still unapplied:** the packet factoring from last turn. Until `exact_ConcreteLambdaJoinedMemoPacketAt` exists, there is nowhere to pass these arguments.
- **Still opaque:** `H` and `U` come from primitive-recursive existence theorems. In the second variant they are reached only where the physical rows fall through.
- **Source guards:** both lemmas keep `singletonLambda` exactly as saved, including its outer syntax guard.

## Compile risks

- Both proofs are direct applications of saved theorems with explicit arguments; I confirmed each signature against its source file this round.
- The new module imports the child-fit module and the shift-hit atoms module together. Neither names the other in its own import list, but I did not trace their transitive imports for a cycle.
