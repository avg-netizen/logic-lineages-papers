module
public import LogicLineages.PermittedControl.SharedRankResidueRowTargets
import LogicLineages.PermittedControl.SharedRankResidueRowCellProof
import LogicLineages.PermittedControl.MixedRankResidueStatementChecks
import Mathlib.Data.Int.ModEq

@[expose] public section
namespace LogicLineages.PermittedControl.SharedRankResidueRow
open PreparedProjection
open MixedSameRankResidue (WeightedOperand weightedResidue)
open MixedRankResidue (Residues rankSupport lookup residueVector originalVector)
open MixedRankNamedResidueRow (toVector)
open RankResidueChoices (actualCell)
open StatementChecks (fixed_actualMultiRankResidue fixed_mixedRankResidueSupport)

private theorem lookupActual (m rank : Nat) (layout : Layout) (ρ : Nat → Nat)
    (member : rank ∈ layout.map Prod.snd) :
    lookup rank (toVector (actualCell m layout ρ)) = ρ rank % (2*m) := by
  induction layout with
  | nil => simp at member
  | cons slot tail ih =>
    change (if slot.2 = rank then ρ slot.2 % (2*m)
      else lookup rank (toVector (actualCell m tail ρ))) = ρ rank % (2*m)
    by_cases same : slot.2 = rank
    · simp [same]
    · rw [if_neg same]
      exact ih ((List.mem_cons.mp member).resolve_left (Ne.symm same))

private theorem vectorAgreement (terms : List WeightedOperand) (p q : Residues)
    (same : ∀ t ∈ terms, lookup t.2.rank p = lookup t.2.rank q) :
    residueVector terms p = residueVector terms q := by
  induction terms with
  | nil => rfl
  | cons t tail ih =>
    change weightedResidue [t] (lookup t.2.rank p) + residueVector tail p =
      weightedResidue [t] (lookup t.2.rank q) + residueVector tail q
    rw [same t List.mem_cons_self,ih (fun w member => same w (List.mem_cons_of_mem _ member))]

theorem actualRowAtLayout : ActualRowAtLayout := by
  intro f B chosen layout r ρ positive covered proper tail
  obtain ⟨values,reads,congruence⟩ :=
    fixed_actualMultiRankResidue f B chosen r.1 r.2.1 r.2.2 ρ positive proper tail
  have vectors : residueVector r.2.2 (toVector (actualCell r.1 layout ρ)) =
      residueVector r.2.2 (originalVector r.1 r.2.2 ρ) := by
    apply vectorAgreement
    intro t read
    have used : t.2.rank ∈ rankSupport r.2.2 :=
      ((fixed_mixedRankResidueSupport.1 r.2.2).2 t.2.rank).mpr ⟨t,read,rfl⟩
    exact (lookupActual r.1 t.2.rank layout ρ (covered _ used)).trans
      (fixed_mixedRankResidueSupport.2 r.1 r.2.2 ρ _ used).symm
  refine ⟨values,reads,?_⟩
  intro ν tied
  refine (formulaAt layout r ρ ν positive tied).trans ?_
  rw [vectors]
  exact congruence.dvd_iff.symm

end LogicLineages.PermittedControl.SharedRankResidueRow
