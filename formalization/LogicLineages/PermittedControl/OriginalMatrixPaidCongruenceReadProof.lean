module
public import LogicLineages.PermittedControl.OriginalMatrixPaidCongruenceTargets
import LogicLineages.PermittedControl.MixedSameRankResidueSemanticProof
import LogicLineages.PermittedControl.MixedRankResidueCodeProof
import Mathlib.Data.Int.ModEq

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalMatrixPaidCongruence
open PreparedProjection (LowerOperand LowerOperandActual lowerOperandRead)
open MixedSameRankResidue (WeightedOperand orderedReads actualSum encodeWeighted weightedResidue
  weightedTailCode properOperand actualWeightedResidue)
open MixedRankResidue (lookup residueVector residueVectorCode)
open SharedRankResidueRow (Layout)
open RankResidueChoices (actualCell)
open MixedRankNamedResidueRow (toVector)

private theorem lookupActual (m : Nat) (ρ : Nat → Nat) (layout : Layout) (k : Nat)
    (used : k ∈ layout.map Prod.snd) :
    lookup k (toVector (actualCell m layout ρ)) = ρ k % (2*m) := by
  induction layout with
  | nil => cases used
  | cons s layout ih =>
      change (if s.2 = k then ρ s.2 % (2*m) else lookup k (toVector (actualCell m layout ρ))) = _
      by_cases same : s.2 = k
      · simp [same]
      · rw [if_neg same]
        exact ih ((List.mem_cons.mp used).resolve_left (Ne.symm same))

private theorem one (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (ρ : Nat → Nat) (m : Nat) (hm : 0 < m) (t : WeightedOperand)
    (proper : properOperand t.2) (paid : weightedTailCode B m [encodeWeighted t] ≤ ρ t.2.rank) :
    ∃ v : Nat, LowerOperandActual f ρ t.2 v ∧ lowerOperandRead f ρ t.2 = some (some v) ∧
      Int.ModEq (m : Int) (t.1 * (v : Int)) (weightedResidue [t] (ρ t.2.rank % (2*m))) := by
  have typed : ∀ u ∈ [t], u.2.rank = t.2.rank ∧ properOperand u.2 := by
    intro u hu
    have eq := List.mem_singleton.mp hu
    subst u
    exact ⟨rfl,proper⟩
  obtain ⟨vs,read,modular⟩ := actualWeightedResidue f B hf m t.2.rank 0 [t] ρ hm typed paid
  cases vs with
  | nil => exact False.elim read
  | cons v vs =>
      cases vs with
      | cons z zs => exact False.elim read.2.2
      | nil =>
          exact ⟨v,read.1,read.2.1,by simpa [actualSum] using modular⟩

private theorem reads (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (ρ : Nat → Nat) (layout : Layout) (m : Nat) (hm : 0 < m) (ts : List WeightedOperand)
    (covered : Covers layout ts) (shape : ∀ t ∈ ts, properOperand t.2) (paid : paidTerms B m ρ ts) :
    ∃ values : List Nat, orderedReads f ρ ts values ∧
      Int.ModEq (m : Int) (actualSum ts values) (residueVector ts (toVector (actualCell m layout ρ))) := by
  induction ts with
  | nil => exact ⟨[],True.intro,Int.ModEq.refl _⟩
  | cons t ts ih =>
      obtain ⟨v,actual,hit,head⟩ := one f B hf ρ m hm t
        (shape t List.mem_cons_self) (paid t List.mem_cons_self)
      obtain ⟨vs,live,tail⟩ := ih
        (fun u hu => covered u (List.mem_cons_of_mem _ hu))
        (fun u hu => shape u (List.mem_cons_of_mem _ hu))
        (fun u hu => paid u (List.mem_cons_of_mem _ hu))
      refine ⟨v :: vs,⟨actual,hit,live⟩,?_⟩
      change Int.ModEq (m : Int) (t.1 * (v : Int) + actualSum ts vs)
        (weightedResidue [t] (lookup t.2.rank (toVector (actualCell m layout ρ))) +
          residueVector ts (toVector (actualCell m layout ρ)))
      rw [lookupActual m ρ layout t.2.rank (covered t List.mem_cons_self)]
      exact head.add tail

theorem exactPaidCongruenceReads : ExactPaidCongruenceReads := by
  intro f B hf ρ layout m c ts hm covered shape paid
  obtain ⟨vs,live,cong⟩ := reads f B hf ρ layout m hm ts covered shape paid
  refine ⟨vs,live,?_⟩
  unfold digitResult
  rw [MixedRankResidue.codeExact.2.2.2 ts]
  exact cong.add_left c

end LogicLineages.PermittedControl.OriginalMatrixPaidCongruence
