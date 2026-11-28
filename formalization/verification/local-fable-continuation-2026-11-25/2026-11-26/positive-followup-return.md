Yes: the saved bridge discharges the numeric calibration on the guarded lambda node. The other lane's `exact_LiteralLambdaDispatchValue` already evaluates the written lambda dispatch for any slot program on any three-slot tape, so no table reasoning or evaluation work is left. The remaining child obligation is the slot program's own contract at `(m, c+1, b)`, and the bridge's first conjunct shows that point is behind the guard. Nothing here is compiled or written.

One thing to know first: the two ShiftCut modules from two turns ago are not on disk (no `*ShiftCut*` file exists). So I state the calibration on the existing program `singletonLambdaDispatch S` read on the tape `[amount, cutoff, code]`, with the cutoff contract written inline. No new program is added.

## Calibration module

`LogicLineages/PersistentMarking/NumberedWindowInternalLiteralSingletonShiftLambdaRowNumericProof.lean`

```lean
module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonLambdaRowsNumericProof
import LogicLineages.PersistentMarking.NumberedWindowShiftLambdaBodyProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonShiftLambdaRowNumericProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open NumberedWindowInternalSparseRawFunctionFrameNumericASTProof (tape)
open NumberedWindowInternalLiteralSingletonLambdaMachineProof (singletonLambdaDispatch)
open NumberedWindowInternalLiteralSingletonLambdaRowsNumericProof
  (exact_LiteralLambdaShapeBit exact_LiteralLambdaShape exact_LiteralLambdaDispatchValue
    exact_LiteralLambdaDispatchOther)
open NumberedWindowShiftLambdaBodyProof (exact_ShiftLambdaRowValue)
open NumberedWindowFieldAlgorithm (unpackNode)
open NumberedWindowSyntaxAlgorithm (syntaxBits)
open NumberedWindowShiftAlgorithm (output)

/-- One guarded lambda node on the tape `[amount,cutoff,code]`. The
written dispatch returns the original shift value as soon as the slot
program returns the original shift value on the body at the incremented
cutoff. That single equation is the whole child obligation. -/
theorem exact_ShiftLambdaDispatchCalibratedRow (S : Program 3) (m c n ty b : Nat)
    (well : (syntaxBits n).1 = true) (node : unpackNode n = some (2,[ty,b]))
    (child : evaluate S (m ::ᵥ (c+1) ::ᵥ b ::ᵥ nil) = ((output m (c+1) b).1).getD 0 + 1) :
    evaluate (singletonLambdaDispatch S) (tape m c n) = ((output m c n).1).getD 0 + 1 := by
  rw [exact_LiteralLambdaDispatchValue S m c n ty b node,child,if_neg (Nat.succ_ne_zero _),
    Nat.pred_succ,(exact_ShiftLambdaRowValue m c n ty b well node).2.2]

/-- The cutoff-general shift contract behind the syntax guard on the code. -/
def GuardedShiftCutFit (S : Program 3) : Prop :=
  ∀ m c n, (syntaxBits n).1 = true →
    evaluate S (m ::ᵥ c ::ᵥ n ::ᵥ nil) = ((output m c n).1).getD 0 + 1

/-- The written lambda dispatch keeps that contract from the slot's
contract alone. The child premise is the same contract at the body and
the incremented cutoff; the body's validity comes from the node's. -/
theorem exact_ShiftLambdaDispatchGuardedFit (S : Program 3) (sFit : GuardedShiftCutFit S) :
    GuardedShiftCutFit (singletonLambdaDispatch S) := by
  intro m c n well
  change evaluate (singletonLambdaDispatch S) (tape m c n) = _
  rcases exact_LiteralLambdaShapeBit n with no | yes
  · rw [exact_LiteralLambdaDispatchOther S m c n no]
    exact sFit m c n well
  · obtain ⟨ty,b,node⟩ := (exact_LiteralLambdaShape n).mp yes
    have row := exact_ShiftLambdaRowValue m c n ty b well node
    exact exact_ShiftLambdaDispatchCalibratedRow S m c n ty b well node
      (sFit m (c+1) b row.1)

#print axioms exact_ShiftLambdaDispatchCalibratedRow
#print axioms GuardedShiftCutFit
#print axioms exact_ShiftLambdaDispatchGuardedFit
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonShiftLambdaRowNumericProof
```

## How it fits together

- **Program evaluation:** `exact_LiteralLambdaDispatchValue` gives the dispatch value as `packNode 2 [ty, pred (child)] + 1` when the child is nonzero. It is stated for an arbitrary `U` and arbitrary first two slots, so it applies verbatim with `U := S`, `a := m`, `d := c`.
- **Original value:** the third conjunct of the saved `exact_ShiftLambdaRowValue` rewrites the node's shift output as the same rebuilt node around the body's output at `c+1`. That is where `exact_ShiftOutput` and the table lemmas enter; they are not repeated here.
- **Child:** the first conjunct gives `(syntaxBits b).1 = true`, so `sFit m (c+1) b` applies.

The first theorem follows the same rewrite chain as the other lane's `exact_LiteralLambdaDispatchCalibratedRow`; the second mirrors `exact_LiteralLambdaDispatchGuardedFit` with `exact_LambdaChildFitOfGuarded` folded in.

## What remains

- **Numeric lambda row:** nothing. The dispatch is guarded-calibrated from the slot's guarded contract alone, and it nests.
- **Opaque child, object level:** the open `child` graph of `S` on a symbolic body is still the course-of-values dependency. This module does not touch it.
- **Link to the installed `ShiftHitFit H`:** not made. The contract here is guarded on purpose: the unguarded dispatch is wrong on an ill-typed lambda code, where the original value is `1`. Two routes exist, and neither is on disk:
  - the `V`-guarded wrapper and cutoff-zero re-taping from the unsaved ShiftCut draft, which would restore a full fit;
  - a guarded variant of the `H` contract. `exact_LiteralShiftedInsertion` calls `fit a d` only with `(syntaxBits a).1 = true` already in scope, so the existing proofs would go through with a guarded hypothesis.

  Say which you want and I will write only that piece.

**Unverified points:**
- The module inherits the pending status of `NumberedWindowShiftLambdaBodyProof` and of the other lane's `LambdaRowsNumericProof`.
- The `rw [child]` step needs the vector in `child` to be written exactly as in `exact_LiteralLambdaDispatchValue`'s statement, which I copied.
