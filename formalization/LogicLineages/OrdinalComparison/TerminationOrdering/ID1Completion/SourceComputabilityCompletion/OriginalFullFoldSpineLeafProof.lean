module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFullFoldSpineSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SpineApplicationProgramsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SpineApplicationSelectedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableRepresentativeRigidityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFullFoldSpineLeafProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc z)
open OriginalFullFoldSpine
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- The existing selected representative preserves the full mark at its
actual input and output. No selected Program is changed or unfolded. -/
theorem leafMarkIff (base : Data) (window : Program 1)
    (out input parameter mark : OrdinaryArithmetic.Term alpha)
    (hw : Nonempty (Derivation body Gamma (OriginalFunctionNeutrality.windowGraph window input parameter)))
    (hv : Nonempty (Derivation body Gamma
      (graph2 (InternalOriginalUniformDescentSelection.validity
        (SpineApplicationTargets.selectedData base window)) (suc z) input parameter)))
    (hl : Nonempty (Derivation body Gamma
      (graph2 (InternalParameterizedCanonicalResultFold.leaf
        (SpineApplicationTargets.selectedData base window)) out input parameter))) :
    Nonempty (Derivation body Gamma (conclusion out input mark)) := by
  have ha := SpineApplicationProof.activeValue base window input parameter hw hv
  exact SpineApplicationSelectedProof.selectedIff base window out input parameter mark ha hl

/-- Closed original opening guards expose the SAME final leaf graph of N. -/
theorem rejectedMarkIff (base : Data) (window : Program 1)
    (out input parameter mark : OrdinaryArithmetic.Term alpha)
    (hw : Nonempty (Derivation body Gamma (OriginalFunctionNeutrality.windowGraph window input parameter)))
    (hv : Nonempty (Derivation body Gamma
      (graph2 (InternalOriginalUniformDescentSelection.validity
        (SpineApplicationTargets.selectedData base window)) (suc z) input parameter)))
    (hn : Nonempty (Derivation body Gamma
      (InternalParameterizedCanonicalResultFold.foldGraph
        (SpineApplicationTargets.selectedData base window) out input parameter)))
    (hz : Nonempty (Derivation body Gamma
      (graph2 (InternalParameterizedApplicationResultStack.openGuardP
        (InternalParameterizedCanonicalResultFold.rootGuard
          (SpineApplicationTargets.selectedData base window))) z input parameter))) :
    Nonempty (Derivation body Gamma (conclusion out input mark)) :=
  leafMarkIff base window out input parameter mark hw hv
    (OriginalVariableRepresentativeRigidityProof.closedLeafGraph
      (SpineApplicationTargets.selectedData base window) out input parameter hz hn)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFullFoldSpineLeafProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFullFoldSpineLeafProof
