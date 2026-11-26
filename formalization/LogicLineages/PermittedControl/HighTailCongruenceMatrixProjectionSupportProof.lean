module
public import LogicLineages.PermittedControl.HighTailCongruenceMatrixProjectionTargets
import LogicLineages.PermittedControl.SignedCongruenceMatrixStatementChecks
import LogicLineages.PermittedControl.PreparedParameterRowsProof
import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsSupportProof

@[expose] public section
namespace LogicLineages.PermittedControl.HighTailCongruenceMatrixProjection
open PreparedProjection
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open SharedRankResidueRow (SourceRow)
open SignedCongruenceMatrix (commonTail formula)
open HighTailNamedRowProjection (lowerGuard)
open StatementChecks (fixed_signedCongruenceMatrixFormulaSupport)

private theorem lowerGuardPlain (name bound : Nat) : PlainPreparedFormula (lowerGuard name bound) := by
  intro a ha s hs
  have onlyAtom : a = .nonnegative (-(bound : Int),[(1,.variable name)]) := by
    simpa only [lowerGuard,LinearRows.atoms,List.mem_singleton] using ha
  subst a
  have onlySummand : s = (1,.variable name) := List.mem_singleton.mp hs
  subst s
  exact ⟨name,rfl⟩

private theorem guardedPlain (B name : Nat) (rows : List SourceRow) :
    PlainPreparedFormula (guarded B name rows) := by
  intro a ha s hs
  rcases List.mem_append.mp ha with inGuard | inMatrix
  · exact lowerGuardPlain name (commonTail B rows) a inGuard s hs
  · exact (fixed_signedCongruenceMatrixFormulaSupport rows).1 a inMatrix s hs

private theorem guardedVars (B name : Nat) (rows : List SourceRow) (i : Nat) :
    i ∈ (guarded B name rows).variables ↔ i = name ∨ i ∈ (formula rows).variables := by
  simp only [guarded,lowerGuard,NormalForm.Formula.variables,NormalForm.Atom.row,
    NormalForm.rowVariables,List.map_cons,List.map_nil,NormalForm.Summand.name,
    List.singleton_append,List.mem_cons]

theorem outputSupport : OutputSupport := by
  intro B name rows
  refine ⟨prepared_plain_isLinear name _ (guardedPlain B name rows),?_⟩
  intro i
  unfold projected
  rw [LinearRowsSupportProof.exactOutputSupport,guardedVars]
  constructor
  · rintro ⟨outside,equal | inMatrix⟩
    · exact (outside equal).elim
    · exact ⟨outside,inMatrix⟩
  · rintro ⟨outside,inMatrix⟩
    exact ⟨outside,Or.inr inMatrix⟩

end LogicLineages.PermittedControl.HighTailCongruenceMatrixProjection
