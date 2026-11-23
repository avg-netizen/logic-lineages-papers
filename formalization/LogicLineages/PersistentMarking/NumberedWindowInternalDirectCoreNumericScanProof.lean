module

public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreNumericTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreNumericSupportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedScanNumericProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreNumericScanProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowDirectAlgorithm (entries readEntry)
open NumberedWindowFieldAlgorithm (unpack)
open NumberedWindowInternalDirectInsertedScanTargets (scan)
open NumberedWindowInternalDirectInsertedScan (exactNumericScan)
open NumberedWindowInternalDirectInsertedRowTargets (expected)
open NumberedWindowInternalDirectCoreNumericTargets
open NumberedWindowInternalDirectCoreNumericSupportProof (decideToNatOne)

private theorem hasMember (rs : List Nat) (d : Nat) :
    (rs.any (fun a => a == d)) = decide (d ∈ rs) := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, beq_iff_eq, decide_eq_true_eq]
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact ha
  · intro hd
    exact ⟨d,hd,rfl⟩

private theorem scanRows (r : Program 3) (positive : Nat → Nat → Nat → Bool) (fit : PositiveFit r positive)
    (removed : Nat) (rs rows : List Nat) (hr : unpack removed = some rs) :
    rows.all (expected r removed) = (entries rows).any (fun es => es.all (entryOK positive rs)) := by
  induction rows with
  | nil => rfl
  | cons a as ih =>
    simp only [List.all_cons,ih]
    cases ha : readEntry a with
    | none => simp [entries,expected,hr,ha]
    | some e =>
      obtain ⟨t,d,w⟩ := e
      cases hs : entries as with
      | none => simp [entries,ha,hs,Option.any]
      | some es =>
        simp only [entries,ha,hs,Option.bind,Option.any,List.all_cons,expected,hr,
          fit d w t,decideToNatOne,entryOK,hasMember]
        change (decide (d ∈ rs) && positive d w t && es.all (entryOK positive rs)) =
          ((t,d,w) :: es).all (entryOK positive rs)
        rfl

/-- Uses the actual ordered scan and the actual original entry decoder;
the assumed positive fit is on [dominator, certificate, target]. -/
theorem exact_NumericInsertionObserver (r : Program 3) (positive : Nat → Nat → Nat → Bool)
    (fit : PositiveFit r positive) (inserted removed : Nat) (rs : List Nat)
    (hr : unpack removed = some rs) :
    evaluate (scan r) (inserted ::ᵥ removed ::ᵥ nil) =
      ((actualEntries inserted).any (fun es => es.all (entryOK positive rs))).toNat := by
  rw [exactNumericScan]
  unfold actualEntries
  cases h : unpack inserted with
  | none => rfl
  | some rows => exact congrArg Bool.toNat (scanRows r positive fit removed rs rows hr)

#print axioms exact_NumericInsertionObserver
end LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreNumericScanProof
