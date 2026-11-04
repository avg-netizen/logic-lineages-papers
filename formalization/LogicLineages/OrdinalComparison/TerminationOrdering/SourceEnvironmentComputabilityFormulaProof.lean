module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceEnvironmentComputabilityFormulaTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceEnvironmentComputabilityFormulaProof
open FirstOrder Language Source PositiveArithmeticOperators SourceComputabilityFormula SourceEnvironmentComputabilityFormula
open SourceComputabilityFormulaSupportProof

theorem actualEnvironmentFormulaAssembly : SourceEnvironmentComputabilityFormulaTargets.ActualEnvironmentFormulaAssembly := by
  intro formulas Gamma P context values
  induction Gamma with
  | nil =>
    change realize P (⊤ : language.Formula (Fin 1 ⊕ Fin 0)) (Sum.elim (fun _ => context) values) ↔ _
    letI := naturalStructure P
    simp [realize]
  | cons tau rest ih =>
    change realize P ((formulas tau).relabel ![Sum.inl 0,Sum.inr 0] ⊓
      (environmentFormula formulas rest).relabel (Sum.map id Fin.succ)) (Sum.elim (fun _ => context) values) ↔ _
    rw [generalConjTruth,generalRelabelTruth,generalRelabelTruth]
    have hh : (Sum.elim (fun _ : Fin 1 => context) values) ∘ ![Sum.inl 0,Sum.inr 0] = ![context,values 0] := by
      funext i
      exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i
    have ht : (Sum.elim (fun _ : Fin 1 => context) values) ∘ Sum.map id (Fin.succ : Fin rest.length → Fin (rest.length+1)) =
        Sum.elim (fun _ : Fin 1 => context) (fun i => values i.succ) := by
      funext i
      cases i <;> rfl
    rw [hh,ht,ih]
    constructor
    · rintro ⟨h0,hs⟩ i
      exact Fin.cases h0 (fun j => hs j) i
    · intro h
      exact ⟨h 0,fun i => h i.succ⟩

theorem actualEnvironmentComputabilityFormula : SourceEnvironmentComputabilityFormulaTargets.ActualEnvironmentComputabilityFormula := by
  intro n arity Delta
  obtain ⟨formulas,h⟩ := SourceComputabilityFormulaProof.actualGeneralFormulaCalibration n arity Delta
  refine ⟨formulas,h,?_⟩
  intro Gamma P context values
  rw [actualEnvironmentFormulaAssembly]
  exact forall_congr' (fun i => h (Gamma.get i) P context (values i))

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceEnvironmentComputabilityFormulaProof
