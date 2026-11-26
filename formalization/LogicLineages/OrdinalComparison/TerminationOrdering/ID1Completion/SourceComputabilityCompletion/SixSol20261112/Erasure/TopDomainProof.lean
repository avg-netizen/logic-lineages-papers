module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.TopDomainTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalErasureCertificateContinuationSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalizedObjectTypedTransportSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableDecoderInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableErasureCertificateProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.TopDomainProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalRecursionGraphStepSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalTagArithmeticSyntaxProof (z)
open InternalTagArithmeticSupportProof (symm)
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedSourceSyntaxProof (numeralRename)
open OriginalTypedDecoderInternalLogicSyntaxProof (equalRename)
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- The actual source decoder reaches its variable clause and the original
index-zero cons equation. In particular the deleted entry is not guessed
from the requested type annotation. -/
theorem sourceTopAt (H G : Program 1) (M W : Program 2)
 (packed raw typ parameter context gamma extended domain : OTerm alpha)
 (hs : Nonempty (Derivation body Delta
  (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) packed parameter)))
 (hv : Nonempty (Derivation body Delta
  (graph1 OriginalRawSyntaxTransport.variableConstructor raw (numeral 0))))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed typ raw)))
 (hq : Nonempty (Derivation body Delta
  (graph2 InternalPairing.pairing parameter context extended)))
 (hc : Nonempty (Derivation body Delta
  (graph2 InternalListCodec.consCode extended domain gamma))) :
 Nonempty (Derivation body Delta (equal domain typ)) := by
 have hf := OriginalTransparentDecoderValidatorCollapsePackedProof.sourceFieldsElim H G M W
  packed parameter typ raw context extended hp hq hs
 have hr := OriginalRawSyntaxTransportInternalVariableSupportProof.variableConstructorPair
  raw (numeral 0) hv
 obtain ⟨he⟩ := OriginalUniverseDecoderInternalAcceptanceLeafProof.variableIff H M W
  raw (numeral 0) typ extended context hr
 obtain ⟨ha⟩ := andRight hf
 have hd : Nonempty (Derivation body Delta
  (OriginalVariableDecoder.graph (numeral 1) typ (numeral 0) extended)) :=
  ⟨Derivation.conjunctionRight
   (Derivation.implicationElimination (Derivation.conjunctionLeft he) ha)⟩
 have hm := OriginalVariableDecoderInternalProof.consZeroElim
  (numeral 1) typ extended domain gamma hc hd
 obtain ⟨heq⟩ := InternalEqualityTestProof.equalityOfAcceptance typ domain hm
 exact ⟨by simpa only [equalEqn] using symm heq⟩

theorem originalSourceTopDomain : TopDomainTargets.OriginalSourceTopDomain := by
 intro H G M W body alpha Delta packed raw typ parameter context gamma extended domain
 let A := graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) packed parameter ⊓
  (graph1 OriginalRawSyntaxTransport.variableConstructor raw (numeral 0) ⊓
  (graph2 InternalPairing.pairing packed typ raw ⊓
  (graph2 InternalPairing.pairing parameter context extended ⊓
   graph2 InternalListCodec.consCode extended domain gamma)))
 have h : Nonempty (Derivation body (A :: Delta) A) :=
  ⟨Derivation.hypothesis List.mem_cons_self⟩
 obtain ⟨hd⟩ := sourceTopAt H G M W packed raw typ parameter context gamma extended domain
  (andLeft h) (andLeft (andRight h)) (andLeft (andRight (andRight h)))
  (andLeft (andRight (andRight (andRight h)))) (andRight (andRight (andRight (andRight h))))
 exact ⟨Derivation.implicationIntroduction hd⟩

/-- SAME-final original Object typing exposes the real source validator;
the checked all-output source collapse supplies the original concrete source
at the actual parameter. No typed/source graph on erased input is assumed. -/
theorem topAtParameter (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
 (context : Nat) (tau : Ty)
 (source target witness gamma extended packed raw domain parameter : OTerm alpha)
 (h : Nonempty (Derivation body Delta
  (OriginalErasureCertificateContinuation.Premise p H G W context tau
   source target witness gamma extended packed raw domain (numeral 0))))
 (hp : Nonempty (Derivation body Delta
  (graph2 InternalPairing.pairing parameter (numeral context) extended))) :
 Nonempty (Derivation body Delta
  (equal domain (numeral (NumberedLeastCodeRepresentative.typeNumber tau)))) := by
 let p0 := OriginalRankGuardedRepresentative.guardedInputs H G W p
 let r := OriginalFinalGuardedRank.refined p H G W
 let D := OriginalLambdaTraversalSelection.finalData r
 let typ : OTerm alpha := numeral (NumberedLeastCodeRepresentative.typeNumber tau)
 have hs := andLeft (andRight (andRight h))
 have hc := andLeft hs
 have hv := andLeft (andRight hs)
 have hpacked := andLeft (andRight (andRight hs))
 have hobject := andRight (andRight (andRight hs))
 have ht := OriginalCanonicalizedObjectTypedTransportSupportProof.outerRecover
  p0 H G W context typ source extended packed parameter
  (andLeft h) (andLeft (andRight h)) hobject hp
 have hparts := InternalOriginalUniformDescentSelectionInternalProof.typedRecover
  D.oldRepresentative (InternalOriginalUniformDescentSelection.validity D) D.member
  packed typ parameter ht
 obtain ⟨hvld⟩ := andLeft (andRight hparts)
 obtain ⟨hcollapse⟩ :=
  OriginalTransparentDecoderValidatorCollapseProof.actualOriginalTransparentDecoderFinalSourceCollapse
   p0 H G W body alpha Delta (numeral 1) packed parameter
 have hsource : Nonempty (Derivation body Delta
  (graph2 (OriginalUniverseDecoder.source H G
   (InternalOriginalUniformContextMembership.contextMember p.base.member) W)
   (numeral 1) packed parameter)) :=
  ⟨Derivation.implicationElimination (Derivation.conjunctionLeft hcollapse) hvld⟩
 exact sourceTopAt H G (InternalOriginalUniformContextMembership.contextMember p.base.member) W
  packed raw typ parameter (numeral context) gamma extended domain hsource hv hpacked hp hc

theorem topFromOriginal (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
 (context : Nat) (tau : Ty)
 (source target witness gamma extended packed raw domain : OTerm alpha)
 (h : Nonempty (Derivation body Delta
  (OriginalErasureCertificateContinuation.Premise p H G W context tau
   source target witness gamma extended packed raw domain (numeral 0)))) :
 Nonempty (Derivation body Delta
  (equal domain (numeral (NumberedLeastCodeRepresentative.typeNumber tau)))) := by
 apply OriginalCanonicalizedObjectTypedTransportSupportProof.parameterCases context extended _
 intro beta rho Theta hrho parameter hp
 simp only [equalRename,numeralRename]
 have h' := renameInto h rho Theta hrho
 simp only [OriginalErasureCertificateContinuation.Premise,conjunctionRename,
  graph1Rename,numeralRename,InternalComputabilityDownwardSyntaxProof.typedRename,
  OriginalErasureCertificateContinuationSyntaxProof.shapeRename,
  InternalComputabilityDownwardSyntaxProof.certificateRename] at h'
 exact topAtParameter p H G W context tau (source.relabel rho) (target.relabel rho)
  (witness.relabel rho) (gamma.relabel rho) (extended.relabel rho) (packed.relabel rho)
  (raw.relabel rho) (domain.relabel rho) parameter h' hp

theorem originalArbitraryDomainTopCollapse : TopDomainTargets.OriginalArbitraryDomainTopCollapse := by
 intro p H G W body alpha Delta context tau
  source target witness gamma extended packed raw domain erasedSource erasedTarget
 let A := OriginalErasureCertificateContinuation.Premise p H G W context tau
  source target witness gamma extended packed raw domain (numeral 0) ⊓
  (graph1 OriginalRawObjectTransport.eraseObjectRaw erasedSource source ⊓
   graph1 OriginalRawObjectTransport.eraseObjectRaw erasedTarget target)
 have h : Nonempty (Derivation body (A :: Delta) A) :=
  ⟨Derivation.hypothesis List.mem_cons_self⟩
 have hinput := andLeft h
 have heq := topFromOriginal p H G W context tau source target witness gamma extended
  packed raw domain hinput
 have hs := andLeft (andRight (andRight hinput))
 have hc := headTransport InternalListCodec.consCode extended domain
  (numeral (NumberedLeastCodeRepresentative.typeNumber tau)) (Fin.cons gamma Fin.elim0)
  (by simpa only [equalEqn] using heq) (andLeft hs)
 have hshape : Nonempty (Derivation body (A :: Delta)
  (OriginalVariableErasureCertificate.TopVariableShape tau source gamma extended packed raw)) :=
  andIntro hc (andRight hs)
 have horiginal : Nonempty (Derivation body (A :: Delta)
  (OriginalVariableErasureCertificate.Premise p H G W context tau
   source target witness gamma extended packed raw)) :=
  andIntro (andLeft hinput) (andIntro (andLeft (andRight hinput))
   (andIntro hshape (andRight (andRight (andRight hinput)))))
 have hcollapse := OriginalVariableErasureCertificateProof.collapse p H G W context tau
  source target witness gamma extended packed raw erasedSource erasedTarget horiginal
  (andLeft (andRight h)) (andRight (andRight h))
 obtain ⟨hout⟩ := andIntro heq hcollapse
 exact ⟨Derivation.implicationIntroduction hout⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.TopDomainProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.TopDomainProof
