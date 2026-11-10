module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationEdgeDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationEquationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarIdentityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationEdgeBridgeProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open UniformCertificateCompletion
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- Specialize the exact actualJ equation at the SAME final tuple retained
by the quotient checker and global source package. -/
theorem finalForward (p : GlobalSourcePackage.Inputs) :
    let r := OriginalApplicationSidecar.finalInputs p
    let data := OuterSelection.data r.base r.window
    ∀ arrow d e function argument out argumentOut parameter : OTerm alpha,
    Nonempty (Derivation body Gamma
      (OriginalNeutralApplication.InputPremises data r.window arrow d e function argument parameter)) →
    Nonempty (Derivation body Gamma
      (InternalParameterizedCanonicalResultFold.foldGraph data argumentOut argument parameter)) →
    Nonempty (Derivation body Gamma
      (InternalParameterizedCanonicalResultFold.applicationGraph data out d e function argument parameter)) →
    Nonempty (Derivation body Gamma (graph4 application out d e function argumentOut)) := by
  dsimp only
  intro arrow d e function argument out argumentOut parameter hi hn hj
  have hid := OriginalApplicationSidecarIdentityProof.actualOriginalApplicationSidecarSelectionIdentity.2 p
  rw [hid.2,hid.1] at hi
  rw [hid.2] at hn hj
  exact OriginalNeutralApplicationEquationProof.forward p.base p.window
    arrow d e function argument out argumentOut parameter hi hn hj

theorem finalBackward (p : GlobalSourcePackage.Inputs) :
    let r := OriginalApplicationSidecar.finalInputs p
    let data := OuterSelection.data r.base r.window
    ∀ arrow d e function argument out argumentOut parameter : OTerm alpha,
    Nonempty (Derivation body Gamma
      (OriginalNeutralApplication.InputPremises data r.window arrow d e function argument parameter)) →
    Nonempty (Derivation body Gamma
      (InternalParameterizedCanonicalResultFold.foldGraph data argumentOut argument parameter)) →
    Nonempty (Derivation body Gamma (graph4 application out d e function argumentOut)) →
    Nonempty (Derivation body Gamma
      (InternalParameterizedCanonicalResultFold.applicationGraph data out d e function argument parameter)) := by
  dsimp only
  intro arrow d e function argument out argumentOut parameter hi hn ha
  have hid := OriginalApplicationSidecarIdentityProof.actualOriginalApplicationSidecarSelectionIdentity.2 p
  rw [hid.2,hid.1] at hi
  rw [hid.2] at hn ⊢
  exact OriginalNeutralApplicationEquationProof.backward p.base p.window
    arrow d e function argument out argumentOut parameter hi hn ha

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationEdgeBridgeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationEdgeBridgeProof
