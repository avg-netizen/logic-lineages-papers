module
public import LogicLineages.PermittedControl.MixedRankResidueTargets
import LogicLineages.PermittedControl.MixedRankResidueSupportProof
import LogicLineages.PermittedControl.MixedSameRankResidueStatementChecks
import Mathlib.Data.Int.ModEq

@[expose] public section
namespace LogicLineages.PermittedControl.MixedRankResidue
open OrdinalComparison PreparedProjection
open MixedSameRankResidue (WeightedOperand encodeWeighted properOperand orderedReads actualSum
  weightedResidue weightedTailCode operandTailCode)
open StatementChecks (fixed_mixedSameRankResidueActual)

private theorem singletonTailLe (B m : Nat) (t : WeightedOperand) (terms : List WeightedOperand)
    (member : t ∈ terms) :
    weightedTailCode B m [encodeWeighted t] ≤ weightedTailCode B m (terms.map encodeWeighted) := by
  induction terms with
  | nil => simp at member
  | cons h ts ih =>
    change _ ≤ max (operandTailCode B m (encodeWeighted h).2)
      (weightedTailCode B m (ts.map encodeWeighted))
    rcases List.mem_cons.mp member with same | later
    · subst t
      have single : weightedTailCode B m [encodeWeighted h] =
          operandTailCode B m (encodeWeighted h).2 := by simp [weightedTailCode]
      rw [single]
      exact le_max_left _ _
    · exact (ih later).trans (le_max_right _ _)

private theorem oneRead (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B) (m : Nat)
    (ρ : Nat → Nat) (hm : 0 < m) (t : WeightedOperand) (proper : properOperand t.2)
    (paid : weightedTailCode B m [encodeWeighted t] ≤ ρ t.2.rank) :
    ∃ v : Nat, LowerOperandActual f ρ t.2 v ∧ lowerOperandRead f ρ t.2 = some (some v) ∧
      Int.ModEq (m : Int) (t.1 * (v : Int)) (weightedResidue [t] (ρ t.2.rank % (2*m))) := by
  have typed : ∀ u ∈ [t], u.2.rank = t.2.rank ∧ properOperand u.2 := by
    intro u mem
    have same : u = t := List.mem_singleton.mp mem
    subst u
    exact ⟨rfl,proper⟩
  obtain ⟨values,read,residue⟩ := fixed_mixedSameRankResidueActual
    f B hf m t.2.rank 0 [t] ρ hm typed paid
  cases values with
  | nil => exact False.elim read
  | cons v vs =>
    cases vs with
    | nil =>
      obtain ⟨actual,original,_⟩ := read
      refine ⟨v,actual,original,?_⟩
      simpa [actualSum] using residue
    | cons w ws => exact False.elim read.2.2

private theorem readVector (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (m : Nat) (ρ : Nat → Nat) (hm : 0 < m) (terms : List WeightedOperand) (entries : Residues)
    (typed : ∀ t ∈ terms, properOperand t.2)
    (paid : ∀ t ∈ terms, weightedTailCode B m [encodeWeighted t] ≤ ρ t.2.rank)
    (residues : ∀ t ∈ terms, lookup t.2.rank entries = ρ t.2.rank % (2*m)) :
    ∃ values : List Nat, orderedReads f ρ terms values ∧
      Int.ModEq (m : Int) (actualSum terms values) (residueVector terms entries) := by
  induction terms with
  | nil => exact ⟨[],True.intro,Int.ModEq.refl _⟩
  | cons t ts ih =>
    obtain ⟨v,actual,read,head⟩ := oneRead f B hf m ρ hm t
      (typed t List.mem_cons_self) (paid t List.mem_cons_self)
    obtain ⟨vs,reads,tail⟩ := ih
      (fun u hu => typed u (List.mem_cons_of_mem _ hu))
      (fun u hu => paid u (List.mem_cons_of_mem _ hu))
      (fun u hu => residues u (List.mem_cons_of_mem _ hu))
    refine ⟨v :: vs,⟨actual,read,reads⟩,?_⟩
    change Int.ModEq (m : Int)
      (t.1 * (v : Int) + actualSum ts vs)
      (weightedResidue [t] (lookup t.2.rank entries) + residueVector ts entries)
    rw [residues t List.mem_cons_self]
    exact head.add tail

theorem actualMultiRankResidue : ActualMultiRankResidue := by
  intro f B hf m c terms ρ hm typed common
  have used (t : WeightedOperand) (member : t ∈ terms) : t.2.rank ∈ rankSupport terms :=
    ((rankSupportExact.1 terms).2 t.2.rank).mpr ⟨t,member,rfl⟩
  have paid (t : WeightedOperand) (member : t ∈ terms) :
      weightedTailCode B m [encodeWeighted t] ≤ ρ t.2.rank :=
    (singletonTailLe B m t terms member).trans (common _ (used t member))
  have residue (t : WeightedOperand) (member : t ∈ terms) :
      lookup t.2.rank (originalVector m terms ρ) = ρ t.2.rank % (2*m) :=
    rankSupportExact.2 m terms ρ _ (used t member)
  obtain ⟨values,reads,relation⟩ := readVector f B hf m ρ hm terms _ typed paid residue
  exact ⟨values,reads,relation.add_left c⟩

end LogicLineages.PermittedControl.MixedRankResidue
