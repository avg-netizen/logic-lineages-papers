module
public import LogicLineages.PermittedControl.SharedRankResidueRowTargets
import LogicLineages.PermittedControl.RankResidueChoicesStatementChecks

@[expose] public section
namespace LogicLineages.PermittedControl.SharedRankResidueRow
open PreparedProjection
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open RankResidueChoices (Slot Cell Assignment)
open MixedRankNamedResidueRow (atom clause rowFrom)
open StatementChecks (fixed_rankResidueLayoutAndChoices)

private theorem clausePlain (m : Nat) (cell : Cell) : PlainPreparedFormula (clause m cell) := by
  induction cell with
  | nil => simp [PlainPreparedFormula,clause,LinearRows.atoms]
  | cons e tail ih =>
    intro a ha s hs
    have parts : a = .divisible (2*m-1) (-(e.2.2 : Int),[(1,.variable e.1)]) ∨
        a ∈ LinearRows.atoms (clause m tail) := by
      simpa only [clause,List.foldr_cons,atom,LinearRows.atoms,List.singleton_append,List.mem_cons] using ha
    rcases parts with equal | later
    · subst a
      have exactSummand : s = (1,.variable e.1) := List.mem_singleton.mp hs
      subst s
      exact ⟨e.1,rfl⟩
    · exact ih a later s hs

private theorem clauseVars (m : Nat) (cell : Cell) (i : Nat) (used : i ∈ (clause m cell).variables) :
    ∃ e ∈ cell, e.1 = i := by
  induction cell with
  | nil => simp [clause,NormalForm.Formula.variables] at used
  | cons e tail ih =>
    have parts : i = e.1 ∨ i ∈ (clause m tail).variables := by
      simpa only [clause,List.foldr_cons,atom,NormalForm.Formula.variables,NormalForm.Atom.row,
        NormalForm.rowVariables,List.map_cons,List.map_nil,NormalForm.Summand.name,
        List.singleton_append,List.mem_cons] using used
    rcases parts with equal | later
    · exact ⟨e,List.mem_cons_self,equal.symm⟩
    · obtain ⟨d,member,same⟩ := ih later
      exact ⟨d,List.mem_cons_of_mem _ member,same⟩

private theorem rowPlain (m : Nat) (retain : Cell → Bool) (cells : List Cell) :
    PlainPreparedFormula (rowFrom m retain cells) := by
  induction cells with
  | nil => simp [rowFrom,PlainPreparedFormula,LinearRows.atoms]
  | cons cell tail ih =>
    by_cases selected : retain cell = true
    · intro a ha s hs
      have parts : a ∈ LinearRows.atoms (clause m cell) ∨
          a ∈ LinearRows.atoms (rowFrom m retain tail) := by
        simpa only [rowFrom,List.foldr_cons,if_pos selected,LinearRows.atoms,List.mem_append] using ha
      exact parts.elim (fun found => clausePlain m cell a found s hs) (fun found => ih a found s hs)
    · simpa only [rowFrom,List.foldr_cons,if_neg selected] using ih

private theorem rowVars (m : Nat) (retain : Cell → Bool) (cells : List Cell) (i : Nat)
    (used : i ∈ (rowFrom m retain cells).variables) : ∃ cell ∈ cells, ∃ e ∈ cell, e.1 = i := by
  induction cells with
  | nil => simp [rowFrom,NormalForm.Formula.variables] at used
  | cons cell tail ih =>
    have further (found : i ∈ (rowFrom m retain tail).variables) :
        ∃ c ∈ cell :: tail, ∃ e ∈ c, e.1 = i := by
      obtain ⟨next,member,place⟩ := ih found
      exact ⟨next,List.mem_cons_of_mem _ member,place⟩
    by_cases selected : retain cell = true
    · have parts : i ∈ (clause m cell).variables ∨ i ∈ (rowFrom m retain tail).variables := by
        simpa only [rowFrom,List.foldr_cons,if_pos selected,NormalForm.Formula.variables,
          List.mem_append] using used
      exact parts.elim (fun found => ⟨cell,List.mem_cons_self,clauseVars m cell i found⟩) further
    · apply further
      simpa only [rowFrom,List.foldr_cons,if_neg selected] using used

private theorem assignmentNames {n : Nat} {ss : List Slot} {cell : Cell} (a : Assignment n ss cell) :
    cell.map Prod.fst = ss.map Prod.fst := by
  induction a with
  | nil => rfl
  | cons _ _ ih => simp only [List.map_cons,ih]

private theorem requestsNames (layout : Layout) :
    (requests layout).map Prod.fst = layout.map Prod.fst := by
  simp [requests,List.map_map,Function.comp_def]

theorem formulaSupport : FormulaSupport := by
  intro layout r
  refine ⟨rowPlain r.1 _ _,?_⟩
  intro i used
  obtain ⟨cell,member,e,atDigit,name⟩ := rowVars r.1 _ _ i used
  have assigned := (fixed_rankResidueLayoutAndChoices.2.2.2.1 r.1 layout cell).mp member
  rw [requestsNames,← assignmentNames assigned]
  exact List.mem_map.mpr ⟨e,atDigit,name⟩

end LogicLineages.PermittedControl.SharedRankResidueRow
