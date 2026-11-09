module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterArithmeticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.ForwardGuardProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterDomainForwardProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition
open InternalOriginalUniformDescentSelection (Data)
open InternalComputabilityApplication InternalAccessibilityRules InternalComputabilityDownward
open SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative
open InternalApplicationStepPeelSupportProof InternalPositiveUnfoldingSupportProof
open GuardedSourceSyntaxProof GammaGuardedSourceSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Instantiate the already checked ORIGINAL forward SAME-Gamma rule at
the actual outer source/typed/guard ASTs. Application-field dispatch leaves
both typedness and guard unchanged. No window or calibration premise. -/
theorem guardForward (oldSrc : SourcePresentation.Data) (oldComp : JointGammaComputability.Data)
    (data : Data) (rawScalar : Program 2) (oldStep : Program 4) (bottom measure window : Program 1)
    (oldVertex oldResult : Program 5) (context : Nat) (α : Type) (tau : Ty) (f g a : OTerm α) :
    let src := Outer.source oldSrc oldComp data rawScalar oldStep bottom measure window
    let comp := Outer.computability oldComp data window oldVertex oldResult
    Nonempty (Derivation (SourcePresentation.sourceBody src context) []
      (((typed comp tau (numeral context) g ⊓ edge src false context f g) ⊓ guarded comp f a).imp
        (guarded comp g a))) := by
  let s0 := Outer.sourceBase oldSrc rawScalar (Outer.rawPositive data oldStep bottom measure) window
  let c0 : JointGammaComputability.Data := { oldComp with typed := Outer.typed data window oldComp.typed }
  have h := SourceComputabilityCompletion.ForwardGuardProof.actualOriginalForwardGuardTransport
    s0 c0 Outer.valid Outer.gamma Outer.tag window context α (numeral (typeNumber tau)) f g a
  simpa only [literalTypedGraph,literalGuardGraph,GuardedSource.literalR,
    typed,edge,edgeProgram,guarded] using h

theorem domainForward (oldSrc : SourcePresentation.Data) (oldComp : JointGammaComputability.Data)
    (data : Data) (rawScalar : Program 2) (oldStep : Program 4) (bottom measure window : Program 1)
    (oldVertex oldResult : Program 5) (context : Nat)
    (hw : evaluate window (List.Vector.ofFn ![context]) = 1) :
    SourceComputabilityCompletion.InverseApplication.DomainForward
      (Outer.source oldSrc oldComp data rawScalar oldStep bottom measure window)
      (Outer.computability oldComp data window oldVertex oldResult) context := by
  intro α sigma tau f g a
  let src := Outer.source oldSrc oldComp data rawScalar oldStep bottom measure window
  let comp := Outer.computability oldComp data window oldVertex oldResult
  let P := domain comp context sigma tau f a ⊓ edge src false context f g
  have hp : Nonempty (Derivation (SourcePresentation.sourceBody src context) [P] P) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hdom := andLeft hp
  have hedge := andRight hp
  have rules := OuterArithmeticProof.arithmeticRules oldSrc oldComp data rawScalar oldStep
    bottom measure window oldVertex oldResult context hw
  have htyped : Nonempty (Derivation (SourcePresentation.sourceBody src context) [P]
      (typed comp (.arrow sigma tau) (numeral context) g)) := by
    obtain ⟨rule⟩ := rules.typedDown α (.arrow sigma tau) f g
    obtain ⟨premise⟩ := andIntro (andLeft (andLeft hdom)) hedge
    exact ⟨Derivation.implicationElimination (weakenClosed rule [P]) premise⟩
  have hguard : Nonempty (Derivation (SourcePresentation.sourceBody src context) [P]
      (guarded comp g a)) := by
    obtain ⟨rule⟩ := guardForward oldSrc oldComp data rawScalar oldStep bottom measure window
      oldVertex oldResult context α (.arrow sigma tau) f g a
    obtain ⟨premise⟩ := andIntro (andIntro htyped hedge) (andRight hdom)
    exact ⟨Derivation.implicationElimination (weakenClosed rule [P]) premise⟩
  have result : Nonempty (Derivation (SourcePresentation.sourceBody src context) [P]
      (domain comp context sigma tau g a)) :=
    andIntro (andIntro htyped (andRight (andLeft hdom))) hguard
  obtain ⟨result⟩ := result
  exact ⟨Derivation.implicationIntroduction result⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterDomainForwardProof
