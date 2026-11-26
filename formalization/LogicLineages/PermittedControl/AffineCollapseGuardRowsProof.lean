module
public import LogicLineages.PermittedControl.AffineCollapseGuardRowsTargets
import LogicLineages.PermittedControl.AffineCollapseGuardRowsReadProof
import LogicLineages.PermittedControl.NaturalAffineGateGraphSemanticProof
import LogicLineages.PermittedControl.FixedHeadCollapseGraphCodeProof
import LogicLineages.OrdinalComparison.RawNotationCode

@[expose] public section
namespace LogicLineages.PermittedControl.AffineCollapseGuardRows
open OrdinalComparison FieldComparison PreparedProjection
open HeterogeneousSignedMatrixSlice (Snapshot actualRows)
open SignedRowSliceValue (valueAt)

private theorem affineValue (f θ : Nat → Nat) (e : NaturalAffineGateGraph.Expression)
    (input : Nat) (a : Int) :
    valueAt f θ e.1 (affineTerms e input) a ↔
      NaturalAffineGateGraph.signedValue e θ - (θ input : Int) = a := by
  change valueAt f θ e.1 (((-1,input) :: e.2).map (fun t => (t.1,.coordinate t.2))) a ↔ _
  rw [coordinatesSum]
  simp only [List.map_cons,List.sum_cons,neg_one_mul,NaturalAffineGateGraph.signedValue]
  let s : Int := (e.2.map (fun t => t.1 * (θ t.2 : Int))).sum
  change e.1 + (-(θ input : Int) + s) = a ↔ (e.1 + s) - (θ input : Int) = a
  rw [sub_eq_add_neg, add_assoc, add_comm s (-(θ input : Int))]

private theorem normValue (f θ : Nat → Nat) (lam : NONote) (input : Nat) (b : Int) :
    valueAt f θ (-(actualOrdinalNorm lam.1.repr : Int)) [(1,.coordinate input)] b ↔
      (θ input : Int) - (actualOrdinalNorm lam.1.repr : Int) = b := by
  change valueAt f θ _ (([(1,input)] : List (Int × Nat)).map (fun t => (t.1,.coordinate t.2))) b ↔ _
  rw [coordinatesSum]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,one_mul,add_zero]
  omega

private theorem hitEqualsRead (f : Nat → Nat) (head x y : Nat) :
    (∃ hit : Nat × Nat, closedProperEntryResult f (head,0,x) = some (some hit) ∧
      hit.1 + hit.2 = y) ↔
    FixedHeadCollapseGraph.read f (head,x) = some y := by
  let R := closedProperEntryResult f (head,0,x)
  change (∃ hit : Nat × Nat, R = some (some hit) ∧ hit.1 + hit.2 = y) ↔
    R.join.map (fun hit => hit.1 + hit.2) = some y
  cases R with
  | none => simp [Option.join]
  | some s =>
      cases s with
      | none => simp [Option.join]
      | some hit =>
          constructor
          · rintro ⟨h,hEq,hSum⟩
            have he : hit = h := Option.some.inj (Option.some.inj hEq)
            subst h
            exact congrArg some hSum
          · intro h
            refine ⟨hit,rfl,?_⟩
            exact Option.some.inj h

private theorem normPaidByHit (f : Nat → Nat) (lam : NONote) (x y : Nat)
    (h : FixedHeadCollapseGraph.read f (rawNoteEncode lam.1,x) = some y) :
    actualOrdinalNorm lam.1.repr ≤ x := by
  have hex := (hitEqualsRead f (rawNoteEncode lam.1) x y).mpr h
  obtain ⟨hit,hh,_⟩ := hex
  have hguard : FixedHeadCollapseGraph.guard (rawNoteEncode lam.1,x) = true := by
    change closedProperEntryGuard (rawNoteEncode lam.1,0,x) = true
    cases hg : closedProperEntryGuard (rawNoteEncode lam.1,0,x)
    · simp [closedProperEntryResult,hg] at hh
    · rfl
  have hd := (FixedHeadCollapseGraph.guardExact.2 _).mp hguard
  change ONote.NF (rawNoteDecode (rawNoteEncode lam.1)) ∧
    Order.IsSuccLimit (rawNoteDecode (rawNoteEncode lam.1)).repr ∧
    actualOrdinalNorm (rawNoteDecode (rawNoteEncode lam.1)).repr ≤ x at hd
  rw [rawNoteDecodeEncode] at hd
  exact hd.2.2

private theorem threeRows (f θ : Nat → Nat) (lam : NONote)
    (e : NaturalAffineGateGraph.Expression) (input output : Nat) (a b c : Int) :
    actualRows f θ (guardRows lam e input output) [(a,true),(b,true),(c,true)] ↔
      (NaturalAffineGateGraph.signedValue e θ - (θ input : Int) = a ∧ a = 0) ∧
      ((θ input : Int) - (actualOrdinalNorm lam.1.repr : Int) = b ∧ 0 ≤ b) ∧
      (valueAt f θ 0 (collapseTerms lam input output) c ∧ c = 0) := by
  simp only [guardRows,actualRows,SignedRowGuardedTest.Test.Admitted,
    SignedRowGuardedTest.Test.atPolarity,SignedRowGuardedTest.Test.Holds,if_true,true_and,and_true,
    affineValue,normValue,and_assoc]

theorem exactAffineCollapseGuardRows : ExactAffineCollapseGuardRows := by
  intro f lam _ e input output θ snapshot
  constructor
  · rintro ⟨hrows,a,b,c,rfl⟩
    obtain ⟨⟨ha,haz⟩,⟨hb,_⟩,⟨hc,hcz⟩⟩ := (threeRows f θ lam e input output a b c).mp hrows
    have hgate : (θ input : Int) = NaturalAffineGateGraph.signedValue e θ := by omega
    obtain ⟨hit,hD,hV⟩ := (collapseValue f θ lam input output c).mp hc
    have hSum : hit.1 + hit.2 = θ output := by omega
    refine ⟨⟨(NaturalAffineGateGraph.signedGraph input e θ).mpr hgate,
      (hitEqualsRead f _ _ _).mp ⟨hit,hD,hSum⟩⟩,?_⟩
    rw [haz,hcz,← hb]
  · rintro ⟨⟨ha,hc⟩,rfl⟩
    have hGate := (NaturalAffineGateGraph.signedGraph input e θ).mp ha
    have hNorm := normPaidByHit f lam (θ input) (θ output) hc
    obtain ⟨hit,hD,hSum⟩ := (hitEqualsRead f _ _ _).mpr hc
    refine ⟨(threeRows f θ lam e input output _ _ _).mpr ?_,⟨_,_,_,rfl⟩⟩
    refine ⟨⟨by omega,rfl⟩,⟨rfl,by omega⟩,
      ⟨(collapseValue f θ lam input output 0).mpr ⟨hit,hD,by omega⟩,rfl⟩⟩

end LogicLineages.PermittedControl.AffineCollapseGuardRows
