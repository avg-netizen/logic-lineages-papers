module
public import LogicLineages.PermittedControl.HighTailNamedRowProjectionTargets
import LogicLineages.PermittedControl.MixedRankNamedResidueRowStatementChecks
import LogicLineages.PermittedControl.PreparedParameterRowsProof
import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsSupportProof

@[expose] public section
namespace LogicLineages.PermittedControl.HighTailNamedRowProjection
open PreparedProjection
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open MixedSameRankResidue (WeightedOperand)
open MixedRankNamedResidueRow (row)
open StatementChecks (fixed_mixedRankNamedResidueRowShapeAndSupport)

theorem lowerGuardEval (name bound : Nat) (ν : Nat → Nat) :
    (lowerGuard name bound).eval ν ↔ bound ≤ ν name := by
  simp only [lowerGuard,NormalForm.Formula.eval,NormalForm.Atom.eval,NormalForm.rowValue,
    List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,NormalForm.Summand.term,
    OrdinalComparison.LayeredComparison.SnyatkovCompletion.Term.value,one_mul,add_zero]
  omega

private theorem lowerGuardPlain (name bound : Nat) : PlainPreparedFormula (lowerGuard name bound) := by
  intro a ha s hs
  have onlyAtom : a = .nonnegative (-(bound : Int),[(1,.variable name)]) := by
    simpa only [lowerGuard,LinearRows.atoms,List.mem_singleton] using ha
  subst a
  have onlySummand : s = (1,.variable name) := List.mem_singleton.mp hs
  subst s
  exact ⟨name,rfl⟩

private theorem guardedPlain (B m name : Nat) (c : Int) (terms : List WeightedOperand) :
    PlainPreparedFormula (guarded B m name c terms) := by
  intro a ha s hs
  rcases List.mem_append.mp ha with tail | rowAtom
  · exact lowerGuardPlain name (coordinateTail B m terms) a tail s hs
  · exact (fixed_mixedRankNamedResidueRowShapeAndSupport m c terms).1 a rowAtom s hs

private theorem guardedVars (B m name : Nat) (c : Int) (terms : List WeightedOperand) (i : Nat) :
    i ∈ (guarded B m name c terms).variables ↔ i = name ∨ i ∈ (row m c terms).variables := by
  simp only [guarded,lowerGuard,NormalForm.Formula.variables,NormalForm.Atom.row,
    NormalForm.rowVariables,List.map_cons,List.map_nil,NormalForm.Summand.name,
    List.singleton_append,List.mem_cons]

theorem outputSupport : OutputSupport := by
  intro B m name c terms
  refine ⟨prepared_plain_isLinear name _ (guardedPlain B m name c terms),?_⟩
  intro i
  unfold projected
  rw [LinearRowsSupportProof.exactOutputSupport,guardedVars]
  constructor
  · rintro ⟨outside,equal | inRow⟩
    · exact (outside equal).elim
    · exact ⟨outside,inRow⟩
  · rintro ⟨outside,inRow⟩
    exact ⟨outside,Or.inr inRow⟩

end LogicLineages.PermittedControl.HighTailNamedRowProjection
