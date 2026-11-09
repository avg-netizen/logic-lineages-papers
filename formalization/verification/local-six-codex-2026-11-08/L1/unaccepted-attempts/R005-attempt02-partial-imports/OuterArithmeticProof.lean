module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceRelationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GammaGuardedSourceRelationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationGuardedApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityDownwardSourceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecEvaluationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterArithmeticProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalOriginalUniformDescentSelection (Data)
open InternalComputabilityApplication InternalAccessibilityRules InternalComputabilityDownward
open SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative
open InternalApplicationStepPeelSupportProof GuardedSourceSyntaxProof GammaGuardedSourceSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The original literal arrow constructor, on every original closed pair
of source type codes. No application function/output is evaluated here. -/
theorem arrowEvaluation (sigma tau : Ty) :
    evaluate Outer.arrow (List.Vector.ofFn ![typeNumber sigma,typeNumber tau]) =
      typeNumber (.arrow sigma tau) := by
  change evaluate InternalListCodec.consCode
    (List.Vector.ofFn ![typeNumber sigma,typeNumber tau]) =
      1 + Nat.pair (typeNumber sigma) (typeNumber tau)
  simpa only [InternalEqualityTestEvaluationProof.vectorTwo,
    Matrix.cons_val_zero,Matrix.cons_val_one] using
      InternalListCodecEvaluationProof.consEvaluation (typeNumber sigma) (typeNumber tau)

/-- All three ORIGINAL arithmetic rules for the actual outer constructors.
Only a closed numeric window evaluation is needed. Raw leaves, markers,
scalar checker, fallback outputs and multiset/direct fields are arbitrary;
no semantic correctness of open terms enters the derivations. -/
theorem arithmeticRules (oldSrc : SourcePresentation.Data) (oldComp : JointGammaComputability.Data)
    (data : Data) (rawScalar : Program 2) (oldStep : Program 4) (bottom measure window : Program 1)
    (oldVertex oldResult : Program 5) (context : Nat)
    (hw : evaluate window (List.Vector.ofFn ![context]) = 1) :
    ArithmeticRules
      (Outer.source oldSrc oldComp data rawScalar oldStep bottom measure window)
      (Outer.computability oldComp data window oldVertex oldResult) context := by
  let src := Outer.source oldSrc oldComp data rawScalar oldStep bottom measure window
  let comp := Outer.computability oldComp data window oldVertex oldResult
  let s0 := Outer.sourceBase oldSrc rawScalar (Outer.rawPositive data oldStep bottom measure) window
  let c0 : JointGammaComputability.Data := { oldComp with typed := Outer.typed data window oldComp.typed }
  let middle := GammaGuardedSource.baseComputability c0 Outer.valid Outer.gamma
  constructor
  · intro α tau f g
    let P := typed comp tau (numeral context) f ⊓ edge src false context f g
    have hp : Nonempty (Derivation (SourcePresentation.sourceBody src context) [P] P) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hf : Nonempty (Derivation (SourcePresentation.sourceBody src context) [P]
        (GuardedSource.literalTyped (GuardedSource.computability middle Outer.tag)
          context (numeral (typeNumber tau)) f)) := by
      simpa only [literalTypedGraph,typed] using andLeft hp
    have he : Nonempty (Derivation (SourcePresentation.sourceBody src context) [P]
        (GuardedSource.literalR
          (GuardedSource.source (GammaGuardedSource.baseSource s0 Outer.gamma)
            middle.typed Outer.tag window) context f g)) := by
      simpa only [GuardedSource.literalR,edge,edgeProgram] using andRight hp
    have hg := GuardedSourceRelationProof.relationClosure
      (body := SourcePresentation.sourceBody src context) (Gamma := [P])
      (GammaGuardedSource.baseSource s0 Outer.gamma) middle Outer.tag window context hw
      (numeral (typeNumber tau)) f g hf he
    have result : Nonempty (Derivation (SourcePresentation.sourceBody src context) [P]
        (typed comp tau (numeral context) g)) := by
      simpa only [literalTypedGraph,typed] using hg
    obtain ⟨result⟩ := result
    exact ⟨Derivation.implicationIntroduction result⟩
  · intro α tau f g a
    have h := GammaGuardedSourceRelationProof.actualOriginalGuardTransport s0 c0
      Outer.valid Outer.gamma Outer.tag window context α (numeral (typeNumber tau)) f g a
    simpa only [literalTypedGraph,literalGuardGraph,GuardedSource.literalR,
      typed,edge,edgeProgram,guarded] using h
  · intro α sigma tau f a
    have h := ApplicationGuardedApplicationProof.actualOriginalTotality
      (SourcePresentation.sourceBody src context) (Outer.baseComputability oldComp data window)
      window Outer.arrow (Outer.result oldComp data window oldVertex oldResult)
      context sigma tau hw (arrowEvaluation sigma tau) α f a
    simpa only [InternalComputabilityDownwardSourceProof.domainLiteral,
      InternalComputabilityDownwardSourceProof.existsLiteral] using h

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterArithmeticProof
