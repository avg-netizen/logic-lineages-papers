module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterCertificateCoordinatesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterInputCasesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityDownwardSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterCertificateLiftProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalOriginalUniformDescentSelection (Data)
open InternalComputabilityApplication InternalAccessibilityRules InternalComputabilityDownward
open InternalApplicationStepPeelSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalGraphCompositionSyntaxProof InternalComputabilityDownwardSyntaxProof
open InternalControlGraphSupportProof (programRename)
open InternalComputabilityApplicationSyntaxProof (acceptedRename)
open SourceComputabilityFormulaSupportProof GuardedSourceSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The original unqualified certificate theorem. All seven coordinate and
raw-output witnesses are discharged by original Program totality inside
this derivation. Its antecedent is exactly CertifiedApplicationLift. -/
theorem certifiedApplicationLift (n : Nat) (arity : Fin n → Nat) (base : Data)
    (hc : InternalOriginalUniformDescentSelection.Calibrated n arity base)
    (window : Program 1) (hw : Path.windowCalibrated n window)
    (oldSrc : SourcePresentation.Data) (oldComp : JointGammaComputability.Data)
    (oldStep : Program 4) (oldVertex oldResult : Program 5)
    (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool)
    (hS : SubtypeClosed (fun typ => typ ∈ S)) :
    CertifiedApplicationLift
      (OuterSelection.source oldSrc oldComp base oldStep window)
      (OuterSelection.computability oldComp base window oldVertex oldResult)
      (OuterSelection.lift base window oldVertex)
      (OrdinaryArithmeticQuotient.contextCode symbols S table) := by
  intro α sigma tau f g a out other witness lifted
  let context := OrdinaryArithmeticQuotient.contextCode symbols S table
  let src := OuterSelection.source oldSrc oldComp base oldStep window
  let comp := OuterSelection.computability oldComp base window oldVertex oldResult
  let lift := OuterSelection.lift base window oldVertex
  let P := (domain comp context sigma tau f a ⊓ certificate src false context f g witness) ⊓
    ((accepted comp sigma tau (numeral context) f a out ⊓
      accepted comp sigma tau (numeral context) g a other) ⊓
      programGraph lift lifted (liftArguments context sigma tau a witness))
  have hp : Nonempty (Derivation (SourcePresentation.sourceBody src context) [P] P) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have result : Nonempty (Derivation (SourcePresentation.sourceBody src context) [P]
      (certificate src false context out other lifted)) := by
    apply OuterInputCasesProof.inputCases (OuterSelection.data base window) window oldVertex
      context sigma tau f g a _
    intro β j gammaCode x y argument parameter rawOut rawOther Theta hj hgamma hx hy ha hpair hvF hvG
    rw [certificateRename]
    have hd := renameInto (andLeft (andLeft hp)) j Theta hj
    have hcert := renameInto (andRight (andLeft hp)) j Theta hj
    have hacceptedF := renameInto (andLeft (andLeft (andRight hp))) j Theta hj
    have hacceptedG := renameInto (andRight (andLeft (andRight hp))) j Theta hj
    have hlift := renameInto (andRight (andRight hp)) j Theta hj
    rw [domainRename] at hd
    rw [certificateRename] at hcert
    rw [acceptedRename] at hacceptedF hacceptedG
    simp only [numeralRename] at hacceptedF hacceptedG
    rw [programRename,liftArgumentsRename] at hlift
    exact OuterCertificateCoordinatesProof.atCoordinates n arity base hc window hw
      oldSrc oldComp oldStep oldVertex oldResult symbols S table hS sigma tau
      (f.relabel j) (g.relabel j) (a.relabel j) (out.relabel j) (other.relabel j)
      (witness.relabel j) (lifted.relabel j) gammaCode x y argument parameter rawOut rawOther
      hgamma hx hy ha hpair hvF hvG hd hcert hacceptedF hacceptedG hlift
  obtain ⟨result⟩ := result
  exact ⟨Derivation.implicationIntroduction result⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterCertificateLiftProof
