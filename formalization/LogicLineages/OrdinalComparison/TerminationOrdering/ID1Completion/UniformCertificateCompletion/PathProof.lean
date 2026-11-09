module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.PathCompatibilityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationPathLiftProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.PathProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open UniformCertificateCompletion.Path UniformCertificateCompletion.PathSupportProof
open UniformCertificateCompletion.PathInvariantProof UniformCertificateCompletion.PathCompatibilityProof
open InternalOriginalUniformContextMembership (normalizeData)
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationStepPeelSupportProof
open SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative

theorem actualOriginalUniformPositiveApplicationPathLift :
    PathTargets.ActualOriginalUniformPositiveApplicationPathLift := by
  intro n arity base hc window hw symbols S table hS oldStep oldVertex body α Delta sigma tau
    parameter gammaCode x y argument certificate out other mapped
  let context := OrdinaryArithmeticQuotient.contextCode symbols S table
  let data := normalizeData base
  let ps := InternalApplicationPathMap.parameters parameter
    (numeral (typeNumber sigma)) (numeral (typeNumber tau)) argument
  let P := positivePremises context data oldStep window oldVertex sigma tau
    parameter gammaCode x y argument certificate out other mapped
  have hp : Nonempty (Derivation body (P :: Delta) P) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hpair := andLeft hp
  have hx := andLeft (andRight hp)
  have ha := andLeft (andRight (andRight hp))
  have hrest := andRight (andRight (andRight hp))
  have hfactor : Nonempty (Derivation body (P :: Delta)
      (invariantFactors context data sigma tau parameter (numeral (typeNumber sigma))
        (numeral (typeNumber tau)) argument x)) :=
    andIntro (pairLeft parameter (numeral context) gammaCode hpair)
      (andIntro (equalReflexive (numeral (typeNumber sigma)))
        (andIntro (equalReflexive (numeral (typeNumber tau))) (andIntro hx ha)))
  have hi := invariantAccept context data sigma tau parameter (numeral (typeNumber sigma))
    (numeral (typeNumber tau)) argument x hfactor
  have hinputs : Nonempty (Derivation body (P :: Delta)
      (InternalParameterizedApplicationPathLift.inputs (edgeChecker data oldStep) (vertex data window oldVertex)
        (invariant context data sigma tau) true ps x y certificate out other mapped)) :=
    andIntro hi hrest
  obtain ⟨result⟩ := InternalParameterizedApplicationPathLiftProof.actualInternalParameterizedPositivePathLift
    body (edgeChecker data oldStep) (vertex data window oldVertex) (invariant context data sigma tau)
    (invariantPreservation context data oldStep sigma tau)
    (edgeCompatibility n arity base hc window hw symbols S table hS oldStep oldVertex sigma tau)
    α (P :: Delta) ps x y certificate out other mapped hinputs
  exact ⟨Derivation.implicationIntroduction result⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.PathProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.PathProof
