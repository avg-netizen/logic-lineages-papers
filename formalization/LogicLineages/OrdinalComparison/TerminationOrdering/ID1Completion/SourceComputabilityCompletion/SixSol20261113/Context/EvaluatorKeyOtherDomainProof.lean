module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyOtherMinimumProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRankGuardedLeafTupleProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorErasureSyntax
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyOtherDomainProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalAcceptanceConjunctionProof
open InternalTagArithmeticSyntaxProof (z suc)
open OriginalTypedDecoderTransportLogicalProof (iffBackward)
open UniformCertificateCompletion EvaluatorKeyPut
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
theorem domainFields (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
 (input parameter : OTerm alpha)
 (hd : Nonempty (Derivation body Delta (Domain p H G W input parameter))) :
 Nonempty (Derivation body Delta
   (OriginalFunctionNeutrality.windowGraph (prepared p H G W).window input parameter ⊓
    graph2 (OriginalUniverseDecoder.source H G (member p H G W) W) (suc z) input parameter)) := by
 exact conjunctionRecover (BottomRepresentative.windowAt (prepared p H G W).window)
   (OriginalTransparentDecoderSelection.transparentInputs H G W (prepared p H G W)).base.oldSource
   (Fin.cons input (Fin.cons parameter Fin.elim0)) (andRight hd)
theorem admitted (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
 (left right parameter : OTerm alpha)
 (hl : Nonempty (Derivation body Delta (Domain p H G W left parameter)))
 (hr : Nonempty (Derivation body Delta (Domain p H G W right parameter)))
 (hs : Nonempty (Derivation body Delta (Same p H G W left right parameter))) :
 Nonempty (Derivation body Delta (SixSol20261113.Erasure.EvaluatorErasureDefinitions.AdmittedPair
   (baseRepresentative p H G W) H G (member p H G W) W left right parameter)) :=
 andIntro (andRight (domainFields p H G W left parameter hl))
   (andIntro (andRight (domainFields p H G W right parameter hr)) hs)
theorem conditionFromDomain (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (input parameter : OTerm alpha)
 (hd : Nonempty (Derivation body Delta (Domain p H G W input parameter))) :
 Nonempty (Derivation body Delta (graph2
   (OriginalRankGuardedLeafTupleProof.condition (minimumInputs p H G W P) H G W)
   (suc z) input parameter)) := by
 let q := minimumInputs p H G W P
 have hf := domainFields p H G W input parameter hd
 have hv := iffBackward (OriginalRankGuardedLeafTupleProof.priorSourceIff q H G W (suc z) input parameter) (andRight hf)
 rw [OriginalRankGuardedLeafTupleProof.conditionProgram]
 exact conjunctionAccept _ _ (Fin.cons input (Fin.cons parameter Fin.elim0)) (andLeft hf) hv
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyOtherDomainProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyOtherDomainProof
