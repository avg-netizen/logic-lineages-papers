module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ArgumentReturnConsQueries
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnSourceCases
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ArgumentReturnDispatchProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedSourceSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
open InternalApplicationStepPeel (graph5)
open InternalApplicationValidityStackAppendFrameQueryProof (weakenProof)
theorem supplierWeaken (Theta : List (Formula alpha)) (children deletions produced first second row : OTerm alpha)
 (inc : ∀ f ∈ Delta, f ∈ Theta)
 (hs : UniformReturnSupplierProof.Supplier body Delta children deletions produced first second row) :
 UniformReturnSupplierProof.Supplier body Theta children deletions produced first second row := by
 intro beta j Xi old results hi ha
 exact hs beta j Xi old results (fun f hf => hi f (inc f hf)) ha
theorem atSupplier (R Q : Program 2) (H : Program 1) (M W : Program 2) (job typed rawJob raw parameter children deletions counts payload frame produced first second row packed rawPayload value gamma c tag rawJobs annotatedPrefix childRow : OTerm alpha)
 (hj : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job (numeral 1) typed)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed (numeral 0) rawJob)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing counts children deletions)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload job counts)))
 (hframe : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (numeral 1) payload)))
 (hpacked : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed (numeral 0) raw)))
 (hf : Nonempty (Derivation body Delta (UniformReturnDefinitions.Framed R frame produced value)))
 (ha : Nonempty (Derivation body Delta (OriginalInternalJobAdmissible.Admissible H M W (numeral 1) (numeral 0) raw gamma c)))
 (htag : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw tag rawPayload)))
 (he : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.expansion rawJobs raw parameter)))
 (hscan : Nonempty (Derivation body Delta (graph5 OriginalHereditaryAnnotatedExpansion.scan annotatedPrefix children (numeral 1) (numeral 0) raw rawJobs)))
 (hm : Nonempty (Derivation body Delta (graph1 (InternalListMap.map (k := 0) (SixSol20261113.Context.ChildContentDefinitions.observationFromJob Q)) childRow annotatedPrefix)))
 (hlen : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph children childRow)))
 (hfirst : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup first (numeral 0) childRow)))
 (hsecond : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup second (numeral 1) childRow)))
 (harity : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) children raw)))
 (hs : UniformReturnSupplierProof.Supplier body Delta children deletions produced first second row) :
 Nonempty (Derivation body Delta (graph2 (OriginalTypedArgumentObservations.argumentObservations Q) value raw parameter)) := by
 have hshape := OriginalInternalJobAdmissibleShapeProof.supportedReturn body H M W alpha Delta (numeral 1) (numeral 0) raw gamma c tag rawPayload ha htag
 apply UniformReturnSourceCases.shapeCases (numeral 1) (numeral 0) raw tag rawPayload _ htag hshape
 · intro Theta hi hzero
   obtain ⟨heq⟩ := hzero
   exact ⟨Derivation.explosion (Derivation.implicationElimination (InternalTagArithmeticSupportProof.sucNeZero (InternalTagArithmeticSyntaxProof.z)) heq)⟩
 · intro Theta hi hrole hnilTag
   have hn := ArgumentReturnNilProof.constructor H M W raw gamma c rawPayload (weakenProof ha hi) hnilTag
   exact ArgumentReturnAtValuesProof.nil R Q job typed rawJob raw parameter children deletions counts payload frame produced first second row packed rawPayload value (weakenProof hj hi) (weakenProof ht hi) (weakenProof hr hi) (weakenProof hc hi) (weakenProof hp hi) (weakenProof hframe hi) (weakenProof hpacked hi) (weakenProof hf hi) hnilTag hn
     (supplierWeaken Theta children deletions produced first second row hi hs)
 · intro Theta hi hrole hconsTag
   exact ArgumentReturnConsQueries.cons R Q job typed rawJob raw parameter children deletions counts payload frame produced first second row packed rawPayload value rawJobs annotatedPrefix childRow (weakenProof hj hi) (weakenProof ht hi) (weakenProof hr hi) (weakenProof hc hi) (weakenProof hp hi) (weakenProof hframe hi) (weakenProof hpacked hi) (weakenProof hf hi) hconsTag (weakenProof he hi) (weakenProof hscan hi) (weakenProof hm hi) (weakenProof hlen hi) (weakenProof hfirst hi) (weakenProof hsecond hi) (weakenProof harity hi)
     (supplierWeaken Theta children deletions produced first second row hi hs)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ArgumentReturnDispatchProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ArgumentReturnDispatchProof
