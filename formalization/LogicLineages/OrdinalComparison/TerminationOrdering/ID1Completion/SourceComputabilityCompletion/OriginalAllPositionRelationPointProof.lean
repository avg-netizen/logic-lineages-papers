module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextAllPositionInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportLogicalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionRelationPointProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open UniformCertificateCompletion
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalApplicationStepPeelSupportProof (sameAccept)
open InternalOriginalUniformVertexPathSupportProof (ternaryValue)
open OriginalTypedDecoderTransportLogicalProof (iffForward iffBackward)
open OriginalClassContextAllPositionObserver
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem atCommon (R : Program 2) (cutoff seed candidate parameter value : OTerm alpha)
 (hs : Nonempty (Derivation body Delta (graph3 (positionObservation R) value cutoff seed parameter)))
 (hc : Nonempty (Derivation body Delta (graph3 (positionObservation R) value cutoff candidate parameter))) :
 Nonempty (Derivation body Delta (graph4 (positionTest R) InternalOriginalStepGuard.one cutoff seed candidate parameter)) := by
 let xs : Fin 4 → OTerm alpha := ![cutoff,seed,candidate,parameter]
 exact sameAccept
   (.composition (positionObservation R) ![.projection 0,.projection 1,.projection 3])
   (.composition (positionObservation R) ![.projection 0,.projection 2,.projection 3]) value xs
   (ternaryValue (positionObservation R) (.projection 0) (.projection 1) (.projection 3) value cutoff seed parameter xs hs (projectionValue 0 xs) (projectionValue 1 xs) (projectionValue 3 xs))
   (ternaryValue (positionObservation R) (.projection 0) (.projection 2) (.projection 3) value cutoff candidate parameter xs hc (projectionValue 0 xs) (projectionValue 2 xs) (projectionValue 3 xs))

/-- Equality rows at one cutoff, using actual observation graph values. -/
theorem rowAt (R : Program 2) (cutoff seed other candidate parameter : OTerm alpha)
 (hso : Nonempty (Derivation body Delta (graph4 (positionTest R) InternalOriginalStepGuard.one cutoff seed other parameter))) :
 Nonempty (Derivation body Delta
   ((graph4 (positionTest R) InternalOriginalStepGuard.one cutoff seed candidate parameter).iff
     (graph4 (positionTest R) InternalOriginalStepGuard.one cutoff other candidate parameter))) := by
 apply programCases (positionObservation R) (Fin.cons cutoff (Fin.cons seed (Fin.cons parameter Fin.elim0))) _
 intro beta j Theta value hj hv
 simp only [OriginalTypedDecoderTransportLogicalProof.iffRename,graph4Rename,InternalOriginalStepGuardSupportProof.oneRename]
 have hso := renameInto hso j Theta hj
 simp only [graph4Rename,InternalOriginalStepGuardSupportProof.oneRename] at hso
 simp only [consTermRename,emptyRename] at hv
 let k := cutoff.relabel j
 let s := seed.relabel j
 let o := other.relabel j
 let c := candidate.relabel j
 let p := parameter.relabel j
 let A := graph4 (positionTest R) InternalOriginalStepGuard.one k s c p
 let B := graph4 (positionTest R) InternalOriginalStepGuard.one k o c p
 have ho := iffForward (OriginalClassContextAllPositionInternalProof.positionOutputIff R k s o p value hso) hv
 have forward : Nonempty (Derivation body (A :: Theta) B) := by
   have hit : Nonempty (Derivation body (A :: Theta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
   have hc := iffForward (OriginalClassContextAllPositionInternalProof.positionOutputIff R k s c p value hit)
     (InternalApplicationValidityStackAppendInductionCoreProof.withHyp hv A)
   exact atCommon R k o c p value (InternalApplicationValidityStackAppendInductionCoreProof.withHyp ho A) hc
 have backward : Nonempty (Derivation body (B :: Theta) A) := by
   have hit : Nonempty (Derivation body (B :: Theta) B) := ⟨Derivation.hypothesis List.mem_cons_self⟩
   have hc := iffForward (OriginalClassContextAllPositionInternalProof.positionOutputIff R k o c p value hit)
     (InternalApplicationValidityStackAppendInductionCoreProof.withHyp ho B)
   exact atCommon R k s c p value (InternalApplicationValidityStackAppendInductionCoreProof.withHyp hv B) hc
 obtain ⟨hf⟩ := forward
 obtain ⟨hb⟩ := backward
 exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionRelationPointProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionRelationPointProof
