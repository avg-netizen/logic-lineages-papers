module
public import LogicLineages.PermittedControl.OriginalMatrixPaidCongruenceTargets
import LogicLineages.PermittedControl.OriginalMatrixPaidCongruenceValueProof
import LogicLineages.PermittedControl.MixedRankResidueSupportProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalMatrixPaidCongruence
open HeterogeneousSignedMatrixSlice (Row Snapshot actualRows)
open SignedRowSliceValue (valueAt)
open SharedRankResidueRow (Layout)
open MixedRankResidue (rankSupport rankSupportExact)

private theorem layoutCoverage (rs : List Row) (r : Row) (hr : r ∈ rs) :
    Covers (rankLayout rs) r.2.2 := by
  intro t ht
  have member : t ∈ rs.flatMap (fun r => r.2.2) := List.mem_flatMap.mpr ⟨r,hr,ht⟩
  have cover : t.2.rank ∈ rankSupport (rs.flatMap (fun r => r.2.2)) :=
    ((rankSupportExact.1 _).2 t.2.rank).mpr ⟨t,member,rfl⟩
  apply List.mem_map.mpr
  exact ⟨(t.2.rank,t.2.rank),List.mem_map.mpr ⟨t.2.rank,cover,rfl⟩,rfl⟩

private theorem layoutTies (ρ : Nat → Nat) (rs : List Row) (s : RankResidueChoices.Slot)
    (member : s ∈ rankLayout rs) : ρ s.1 = ρ s.2 := by
  obtain ⟨k,_,rfl⟩ := List.mem_map.mp member
  rfl

private theorem atTest (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (ρ : Nat → Nat) (layout : Layout) (tied : ∀ s ∈ layout, ρ s.1 = ρ s.2)
    (r : Row) (v : Int) (b : Bool) (adm : r.1.Admitted)
    (reads : valueAt f ρ r.2.1 r.2.2 v) (covered : Covers layout r.2.2)
    (paid : paidRow B ρ r) :
    r.1.atPolarity b v ↔ testAt ρ layout r v b := by
  rcases r with ⟨test,c,ts⟩
  cases test with
  | equalZero => rfl
  | nonnegative => rfl
  | positive => rfl
  | congruence m =>
      have exactFormula := exactPaidCongruenceAtValue f B hf ρ ρ layout m c ts v
        adm covered paid tied reads
      cases b with
      | true => exact exactFormula.symm
      | false => exact not_congr exactFormula.symm

private theorem atMatrix (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (ρ : Nat → Nat) (layout : Layout) (tie : ∀ s ∈ layout, ρ s.1 = ρ s.2)
    (rs : List Row) (paid : ∀ r ∈ rs, paidRow B ρ r)
    (covered : ∀ r ∈ rs, Covers layout r.2.2) (snap : Snapshot) :
    actualRows f ρ rs snap ↔ enabledRows f ρ layout rs snap := by
  induction rs generalizing snap with
  | nil => cases snap <;> rfl
  | cons r rs ih =>
      cases snap with
      | nil => rfl
      | cons v vs =>
          rcases v with ⟨v,b⟩
          have tests := atTest f B hf ρ layout tie r v b
          have rest := ih (fun r hr => paid r (List.mem_cons_of_mem _ hr))
            (fun r hr => covered r (List.mem_cons_of_mem _ hr)) vs
          have field := covered r List.mem_cons_self
          have bound := paid r List.mem_cons_self
          constructor
          · rintro ⟨adm,value,test,tail⟩
            exact ⟨adm,value,(tests adm value field bound).mp test,rest.mp tail⟩
          · rintro ⟨adm,value,test,tail⟩
            exact ⟨adm,value,(tests adm value field bound).mpr test,rest.mpr tail⟩

theorem exactPaidCongruenceMatrix : ExactPaidCongruenceMatrix := by
  intro f B hf ρ rs paid snap
  exact atMatrix f B hf ρ (rankLayout rs) (layoutTies ρ rs) rs paid (layoutCoverage rs) snap

end LogicLineages.PermittedControl.OriginalMatrixPaidCongruence
