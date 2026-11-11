module
public meta import LogicLineages.Audit
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSpineGuardLeafTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSpineGuardLeafInternalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open OriginalSpineGuardLeaf
open OriginalConstructorLeaf (accepted OriginalFactor)
open UniformCertificateCompletion
open InternalAcceptanceConjunctionProof
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem originalFactor (oldStep : Program 4) : OriginalFactor oldStep (refined oldStep) := by
  intro body alpha Delta source target certificate parameter
  let P := accepted (refined oldStep) source target certificate parameter
  let xs : Fin 4 → OTerm alpha :=
    Fin.cons source (Fin.cons target (Fin.cons certificate (Fin.cons parameter Fin.elim0)))
  have hp : Nonempty (Derivation body (P :: Delta) P) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := andLeft (conjunctionRecover oldStep
    (PositiveGuard.spineGuard BottomSpineMeasure.measure) xs hp)
  exact ⟨Derivation.implicationIntroduction h⟩

theorem leafHasSpineGuard (oldStep : Program 4) : LeafHasSpineGuard (refined oldStep) := by
  intro body alpha Delta source target certificate parameter
  let P := accepted (refined oldStep) source target certificate parameter
  let xs : Fin 4 → OTerm alpha :=
    Fin.cons source (Fin.cons target (Fin.cons certificate (Fin.cons parameter Fin.elim0)))
  have hp : Nonempty (Derivation body (P :: Delta) P) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := andRight (conjunctionRecover oldStep
    (PositiveGuard.spineGuard BottomSpineMeasure.measure) xs hp)
  exact ⟨Derivation.implicationIntroduction h⟩

/-- Additional conjunction wrappers keep the entire old leaf factor. -/
theorem conjunctionPreserves (leaf extra : Program 4) (h : LeafHasSpineGuard leaf) :
    LeafHasSpineGuard (InternalAcceptance.conjunction leaf extra) := by
  intro body alpha Delta source target certificate parameter
  let P := accepted (InternalAcceptance.conjunction leaf extra) source target certificate parameter
  let xs : Fin 4 → OTerm alpha :=
    Fin.cons source (Fin.cons target (Fin.cons certificate (Fin.cons parameter Fin.elim0)))
  have hp : Nonempty (Derivation body (P :: Delta) P) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hf⟩ := andLeft (conjunctionRecover leaf extra xs hp)
  obtain ⟨hlaw⟩ := h body alpha (P :: Delta) source target certificate parameter
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination hlaw hf)⟩

theorem actualOriginalSpineGuardLeafInternalCases :
    OriginalSpineGuardLeafTargets.ActualOriginalSpineGuardLeafInternalCases := by
  intro oldStep
  exact ⟨originalFactor oldStep,leafHasSpineGuard oldStep⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSpineGuardLeafInternalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSpineGuardLeafInternalProof
