module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaFactorProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open OriginalHereditaryLambda
open InternalAcceptanceConjunctionProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The whole old leaf is retained literally as the first conjunction factor. -/
theorem originalFactor (oldStep : Program 4) :
    OriginalConstructorLeaf.OriginalFactor oldStep (refined oldStep) := by
  intro body alpha Delta source target certificate parameter
  let P := accepted (refined oldStep) source target certificate parameter
  let xs : Fin 4 → OTerm alpha :=
    Fin.cons source (Fin.cons target (Fin.cons certificate (Fin.cons parameter Fin.elim0)))
  have hp : Nonempty (Derivation body (P :: Delta) P) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := conjunctionRecover oldStep (guard oldStep) xs hp
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionLeft h)⟩

/-- The same original four-input guard is retained as the second factor. -/
theorem leafHasGuard (oldStep : Program 4) : LeafHasGuard oldStep (refined oldStep) := by
  intro body alpha Delta source target certificate parameter
  let P := accepted (refined oldStep) source target certificate parameter
  let xs : Fin 4 → OTerm alpha :=
    Fin.cons source (Fin.cons target (Fin.cons certificate (Fin.cons parameter Fin.elim0)))
  have hp : Nonempty (Derivation body (P :: Delta) P) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := conjunctionRecover oldStep (guard oldStep) xs hp
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionRight h)⟩

theorem actualOriginalHereditaryLambdaInternalFactors :
    OriginalHereditaryLambdaTargets.ActualOriginalHereditaryLambdaInternalFactors := by
  intro oldStep
  exact ⟨originalFactor oldStep,leafHasGuard oldStep⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaFactorProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaFactorProof
