module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceSubstitutionEnvironmentTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceSubstitutionEnvironmentProof
open Source NumberedRewriteSyntax NumberedLeastCodeRepresentative PositiveArithmeticOperators SourceComputabilityFormula
open SourceEnvironmentComputabilityFormula SourceSubstitutionEnvironment

theorem actualVariableAtIndex : SourceSubstitutionEnvironmentTargets.ActualVariableAtIndex := by
  intro Gamma
  induction Gamma with
  | nil => intro i; exact Fin.elim0 i
  | cons tau rest ih =>
    intro i
    refine Fin.cases rfl (fun j => ?_) i
    change SourceTypedPorts.variableIndex (variableAt rest j) + 1 = j.val + 1
    rw [ih]

theorem actualVariableAtExhaustive : SourceSubstitutionEnvironmentTargets.ActualVariableAtExhaustive := by
  intro Gamma tau v
  induction v with
  | here => exact ⟨0,rfl⟩
  | @there Gamma tau sigma v ih =>
    obtain ⟨i,he⟩ := ih
    refine ⟨i.succ,?_⟩
    exact congrArg (fun p : Sigma (Variable Gamma) =>
      (⟨p.1,Variable.there p.2⟩ : Sigma (Variable (sigma :: Gamma)))) he

theorem actualSubstitutionEnvironmentFormula : SourceSubstitutionEnvironmentTargets.ActualSubstitutionEnvironmentFormula := by
  intro n arity Delta formulas hform symbols S Gamma theta P context
  rw [SourceEnvironmentComputabilityFormulaProof.actualEnvironmentFormulaAssembly]
  constructor
  · intro h tau v
    obtain ⟨i,he⟩ := actualVariableAtExhaustive Gamma tau v
    have hp : (fun p : Sigma (Variable Gamma) => Computable n arity Delta P context p.1
        (representativeCode symbols S ⟨p.1,theta p.2⟩)) ⟨Gamma.get i,variableAt Gamma i⟩ :=
      (hform (Gamma.get i) P context (substitutionValues symbols S theta i)).mp (h i)
    rw [he] at hp
    exact hp
  · intro h i
    exact (hform (Gamma.get i) P context (substitutionValues symbols S theta i)).mpr
      (h (Gamma.get i) (variableAt Gamma i))

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceSubstitutionEnvironmentProof
