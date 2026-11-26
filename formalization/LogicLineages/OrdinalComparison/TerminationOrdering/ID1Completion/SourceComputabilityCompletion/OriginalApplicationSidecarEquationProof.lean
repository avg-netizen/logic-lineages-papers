module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarEquationSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarEquationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open OriginalApplicationSidecar OriginalApplicationSidecarEquationSupportProof
open InternalApplicationCertificateConstructors InternalApplicationStepPeelSupportProof
open InternalApplicationValidityClosure (applicationConstructors)

/-- Specialize the existing exact internal stack/combine equation. The
unchanged actual root guard is paid by parent validity, not a window premise
or a new sidecar output-success, fixedness or calibration assumption. -/
theorem actualOriginalApplicationSidecarApplicationEquation :
    OriginalApplicationSidecarTargets.ActualOriginalApplicationSidecarApplicationEquation := by
  intro body data window alpha Delta arrow d e fp ap fn arg parent functionOut argumentOut out parameter
  let P := applicationConstructors arrow d e fp ap fn arg parent ⊓
    (graph2 (InternalOriginalUniformDescentSelection.validity (originalData data window))
      InternalOriginalStepGuard.one parent parameter ⊓
      (graph2 (fold data window) functionOut fn parameter ⊓
        graph2 (fold data window) argumentOut arg parameter))
  let A := graph2 (fold data window) out parent parameter
  let B := graph4 application out d e functionOut argumentOut
  have hp : Nonempty (Derivation body (A :: P :: Delta) P) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  obtain ⟨forward⟩ := applicationBackward data window arrow d e fp ap fn arg parent
    functionOut argumentOut out parameter (andLeft hp) (andLeft (andRight hp))
    (andLeft (andRight (andRight hp))) (andRight (andRight (andRight hp)))
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hp' : Nonempty (Derivation body (B :: P :: Delta) P) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  obtain ⟨backward⟩ := applicationForward data window arrow d e fp ap fn arg parent
    functionOut argumentOut out parameter (andLeft hp') (andLeft (andRight hp'))
    (andLeft (andRight (andRight hp'))) (andRight (andRight (andRight hp')))
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction forward) (Derivation.implicationIntroduction backward))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarEquationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarEquationProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarEquationProof.actualOriginalApplicationSidecarApplicationEquation
