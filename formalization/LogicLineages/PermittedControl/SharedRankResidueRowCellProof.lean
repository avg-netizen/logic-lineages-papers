module
public import LogicLineages.PermittedControl.SharedRankResidueRowTargets
import LogicLineages.PermittedControl.RankResidueChoicesStatementChecks
import Mathlib.Data.Int.ModEq

@[expose] public section
namespace LogicLineages.PermittedControl.SharedRankResidueRow
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open MixedRankResidue (residueVector)
open RankResidueChoices (Slot Cell Assignment actualCell choices)
open MixedRankNamedResidueRow (atom clause rowFrom toVector)
open MixedNamedResidueRow (keep)
open StatementChecks (fixed_rankResidueLayoutAndChoices)

private theorem atomEval (m name j : Nat) (positive : 0 < m) (ν : Nat → Nat) :
    (atom m name j).eval ν ↔ Nat.ModEq (2*m) j (ν name) := by
  have modulus : 2*m-1+1 = 2*m := by omega
  have shift : -(j : Int) + (ν name : Int) = (ν name : Int) - j := by omega
  simp only [atom,NormalForm.Formula.eval,NormalForm.Atom.eval,NormalForm.rowValue,
    List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,NormalForm.Summand.term,
    OrdinalComparison.LayeredComparison.SnyatkovCompletion.Term.value,one_mul,add_zero,modulus]
  rw [shift]
  exact Int.modEq_iff_dvd.symm.trans Int.natCast_modEq_iff

private theorem clauseAt (m : Nat) (positive : 0 < m) (ρ ν : Nat → Nat)
    {layout : List Slot} {cell : Cell} (assigned : Assignment (2*m) layout cell)
    (tied : ∀ s ∈ layout, ν s.1 = ρ s.2) :
    (clause m cell).eval ν ↔ cell = actualCell m layout ρ := by
  induction assigned with
  | nil => simp [clause,actualCell,NormalForm.Formula.eval]
  | @cons s j ss tail within assignment ih =>
    have agree := tied s List.mem_cons_self
    have tailAt := ih (fun u hu => tied u (List.mem_cons_of_mem _ hu))
    have digitExact : Nat.ModEq (2*m) j (ρ s.2) ↔ j = ρ s.2 % (2*m) := by
      change j % (2*m) = ρ s.2 % (2*m) ↔ _
      rw [Nat.mod_eq_of_lt within]
    change ((atom m s.1 j).eval ν ∧ (clause m tail).eval ν) ↔
      (s.1,s.2,j) :: tail = (s.1,s.2,ρ s.2 % (2*m)) :: actualCell m ss ρ
    simp only [atomEval m s.1 j positive ν,agree,digitExact,tailAt,List.cons.injEq,
      Prod.mk.injEq,eq_self,true_and]

private theorem rowFromEval (m : Nat) (retain : Cell → Bool) (cells : List Cell) (ν : Nat → Nat) :
    (rowFrom m retain cells).eval ν ↔
      ∃ cell ∈ cells, retain cell = true ∧ (clause m cell).eval ν := by
  induction cells with
  | nil => simp [rowFrom,NormalForm.Formula.eval]
  | cons cell tail ih =>
    change ((if retain cell then .disjunction (clause m cell) (rowFrom m retain tail)
      else rowFrom m retain tail) : NormalForm.Formula).eval ν ↔ _
    by_cases selected : retain cell = true
    · rw [if_pos selected]
      change ((clause m cell).eval ν ∨ (rowFrom m retain tail).eval ν) ↔ _
      rw [ih]
      constructor
      · rintro (holds | ⟨r,mem,keep,holds⟩)
        · exact ⟨cell,List.mem_cons_self,selected,holds⟩
        · exact ⟨r,List.mem_cons_of_mem _ mem,keep,holds⟩
      · rintro ⟨r,mem,keep,holds⟩
        rcases List.mem_cons.mp mem with equal | later
        · subst r
          exact Or.inl holds
        · exact Or.inr ⟨r,later,keep,holds⟩
    · rw [if_neg selected,ih]
      constructor
      · rintro ⟨r,mem,keep,holds⟩
        exact ⟨r,List.mem_cons_of_mem _ mem,keep,holds⟩
      · rintro ⟨r,mem,keep,holds⟩
        rcases List.mem_cons.mp mem with equal | later
        · subst r
          exact (selected keep).elim
        · exact ⟨r,later,keep,holds⟩

private theorem keepExact (m : Nat) (value : Int) : keep m value = true ↔ (m : Int) ∣ value := by
  simp only [keep,decide_eq_true_eq]
  rw [← Nat.dvd_iff_mod_eq_zero,← Int.natAbs_dvd_natAbs,Int.natAbs_natCast]

theorem formulaAt (layout : Layout) (r : SourceRow) (ρ ν : Nat → Nat) (positive : 0 < r.1)
    (tied : ∀ s ∈ layout, ν s.1 = ρ s.2) :
    (formula layout r).eval ν ↔
      (r.1 : Int) ∣ r.2.1 + residueVector r.2.2 (toVector (actualCell r.1 layout ρ)) := by
  unfold formula
  rw [rowFromEval]
  constructor
  · rintro ⟨cell,member,retained,holds⟩
    have assigned := (fixed_rankResidueLayoutAndChoices.2.2.2.1 r.1 layout cell).mp member
    have equal := (clauseAt r.1 positive ρ ν assigned tied).mp holds
    subst cell
    exact (keepExact _ _).mp retained
  · intro divisible
    let cell := actualCell r.1 layout ρ
    have member : cell ∈ choices r.1 layout :=
      fixed_rankResidueLayoutAndChoices.2.2.2.2 r.1 layout ρ positive
    have assigned := (fixed_rankResidueLayoutAndChoices.2.2.2.1 r.1 layout cell).mp member
    exact ⟨cell,member,(keepExact _ _).mpr divisible,(clauseAt r.1 positive ρ ν assigned tied).mpr rfl⟩

end LogicLineages.PermittedControl.SharedRankResidueRow
