module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceFiniteComputabilityFormulaTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceFiniteComputabilityFormulaProof
open FirstOrder Language Source PositiveArithmeticOperators SourceComputabilityFormula NumberedLeastCodeRepresentative SourceFiniteComputabilityFormula
open PositiveArithmeticOperatorsSupportProof SourceComputabilityFormulaSupportProof

theorem typeGuardTruth (tau : Ty) (P : Nat → Prop) (context typ value : Nat) :
    realize P (typeGuard tau) ![context,typ,value] ↔ typ = typeNumber tau := by
  rw [typeGuard,embeddingTruth,Formula.realize_equal]
  rw [numeralTruth]
  rfl

theorem reindexTruth (phi : language.Formula (Fin 2)) (P : Nat → Prop) (context typ value : Nat) :
    realize P (phi.relabel ![0,2]) ![context,typ,value] ↔ realize P phi ![context,value] := by
  rw [generalRelabelTruth]
  have he : ![context,typ,value] ∘ ![0,2] = ![context,value] := by
    funext i
    exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i
  rw [he]

theorem generalSupTruth {α : Type} (p q : language.Formula α) (P : Nat → Prop) (v : α → Nat) :
    realize P (p ⊔ q) v ↔ realize P p v ∨ realize P q v := by
  letI := naturalStructure P
  exact Formula.realize_sup

theorem actualFiniteFormulaAssembly : SourceFiniteComputabilityFormulaTargets.ActualFiniteFormulaAssembly := by
  intro formulas S P context typ value
  induction S with
  | nil =>
    change realize P (⊥ : language.Formula (Fin 3)) ![context,typ,value] ↔ _
    letI := naturalStructure P
    simp [realize,Formula.realize_bot]
  | cons tau rest ih =>
    change realize P ((typeGuard tau ⊓ (formulas tau).relabel ![0,2]) ⊔ windowFormula formulas rest) _ ↔ _
    rw [generalSupTruth,generalConjTruth,typeGuardTruth,reindexTruth,ih]
    simp

theorem actualWindowComputabilityFormula : SourceFiniteComputabilityFormulaTargets.ActualWindowComputabilityFormula := by
  intro n arity Gamma
  obtain ⟨formulas,h⟩ := SourceComputabilityFormulaProof.actualGeneralFormulaCalibration n arity Gamma
  refine ⟨formulas,h,?_,?_⟩
  · intro S P context typ value
    rw [actualFiniteFormulaAssembly]
    exact exists_congr (fun tau => and_congr_right (fun _ => and_congr_right (fun _ => h tau P context value)))
  · intro S P context typ value hbad hyes
    obtain ⟨tau,_,he,_⟩ := (actualFiniteFormulaAssembly formulas S P context typ value).mp hyes
    rw [he,NumberedNumericDecodingProof.typeNumericRoundTrip] at hbad
    cases hbad

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceFiniteComputabilityFormulaProof
