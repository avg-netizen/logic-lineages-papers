module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationLambdaSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyOtherDomainProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyDomainClosureProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationLambdaCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andLeft andRight andIntro)
open InternalGraphCompositionFunctionalityProof (renameInto)
open OriginalLambdaTraversalInternal
open UniformCertificateCompletion EvaluatorKeyPut
open EvaluatorKeyCanonicalInductionDefinitions (C)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open EvaluatorKeyCanonicalPreservationInductionDefinitions
/-- All recursive facts are paid by the actual smaller-payload IH. This
packet contains no parent evaluator equality and uses no congruence supplier. -/
theorem atOutput (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (q input out parameter d e child childParameter childPayload childOut : OTerm alpha)
 (hb : Nonempty (Derivation body Delta (belowPayload p H G W P q)))
 (hp : Nonempty (Derivation body Delta (Premises p H G W P input out parameter)))
 (hf : Nonempty (Derivation body Delta (LambdaFields input d e child parameter childParameter)))
 (hr : Nonempty (Derivation body Delta (graph1 InternalUnpair.right childPayload child)))
 (hlt : Nonempty (Derivation body Delta (InternalLessThan.strictLess childPayload q)))
 (hc : Nonempty (Derivation body Delta (graph2 (C p H G W P) childOut child childParameter))) :
 Nonempty (Derivation body Delta (SixSol20261113.Erasure.EvaluatorErasureDefinitions.AdmittedPair
   (baseRepresentative p H G W) H G (member p H G W) W child childOut childParameter)) ∧
 Nonempty (Derivation body Delta (Domain p H G W out parameter)) ∧
 Nonempty (Derivation body Delta (graph3 OriginalLambdaConstructor.constructor out d e childOut)) ∧
 Nonempty (Derivation body Delta (graph1 InternalUnpair.left e childOut)) := by
 have hd := andLeft hp
 have hC := andRight hp
 have hchildDomain := EvaluatorKeyDomainClosureProof.actualLambdaDomain p H G W body alpha Delta
   input parameter d e child childParameter hd hf
 have hi := EvaluatorKeyCanonicalPreservationBindingProof.belowPayloadApply p H G W P q
   childPayload child childOut childParameter hb hlt hr (andIntro hchildDomain hc)
 have ha := EvaluatorKeyOtherDomainProof.admitted p H G W child childOut childParameter
   hchildDomain (andLeft hi) (andRight hi)
 have hout := EvaluatorKeyCanonicalDomainProof.actualCanonicalDomain p H G W P body alpha Delta
   input out parameter hd hC
 have hcons := OriginalLambdaTraversalInternalLambdaProof.lambdaForward
   (OriginalLambdaTraversalSelection.leaf (refined p H G W P).base (refined p H G W P).window)
   input d e child parameter childParameter childOut out hf hc hC
 have ht := OriginalLambdaTraversalLambdaSelectorProof.bodyType input e child
   (andLeft (andRight (andRight hf))) (andLeft (andRight (andRight (andRight hf))))
 have htype := EvaluatorKeyCanonicalPreservationLambdaSupportProof.outputType p H G W P
   child childOut childParameter e hchildDomain hc ht
 exact ⟨ha,hout,hcons,htype⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationLambdaCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationLambdaCoreProof
