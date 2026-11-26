module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedDirectBottomProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomFreshZeroEndpointProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomRankedNonbottomProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomEndpointProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalTransparentMixedDirectBottom
open InternalTagArithmeticSyntaxProof (suc z)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem rawAcceptance (H G : Program 1) (M W : Program 2) (oldStep : Program 4)
 (s t cert parameter : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (graph1 OriginalTransparentDirectBottom.certificateCode cert s)))
 (h : Nonempty (Derivation body Delta (graph4 (leaf H G M W oldStep) (suc z) s t cert parameter))) :
 Nonempty (Derivation body Delta (graph4 (OriginalTransparentDirectBottom.refined (source H G M W) oldStep) (suc z) s t cert parameter)) :=
 OriginalTransparentMixedPathNilProof.elimination (source H G M W)
  (OriginalTransparentDirectBottom.refined (source H G M W) oldStep) (suc z) s t cert parameter
  (OriginalTransparentVariableStepHereditaryProof.certificatePath s cert hc) h

theorem endpoint (H G : Program 1) (M W : Program 2) (oldStep : Program 4)
 (s t cert parameter typ : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (graph1 OriginalTransparentDirectBottom.certificateCode cert s)))
 (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left typ s)))
 (h : Nonempty (Derivation body Delta (graph4 (leaf H G M W oldStep) (suc z) s t cert parameter))) :
 Nonempty (Derivation body Delta (graph1 BottomRepresentative.bottomCode t typ)) :=
 OriginalTransparentDirectBottomFreshZeroEndpointProof.rawEndpoint (source H G M W) oldStep s t cert parameter typ hc ht
  (rawAcceptance H G M W oldStep s t cert parameter hc h)

theorem nonbottom (H G : Program 1) (M W : Program 2) (oldStep : Program 4)
 (s t cert parameter : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (graph1 OriginalTransparentDirectBottom.certificateCode cert s)))
 (h : Nonempty (Derivation body Delta (graph4 (leaf H G M W oldStep) (suc z) s t cert parameter))) :
 Nonempty (Derivation body Delta (BottomRepresentative.bottomGraph (suc z) s).not) :=
 OriginalTransparentDirectBottomRankedNonbottomProof.rawNonbottom (source H G M W) oldStep s t cert parameter hc
  (rawAcceptance H G M W oldStep s t cert parameter hc h)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomEndpointProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomEndpointProof
