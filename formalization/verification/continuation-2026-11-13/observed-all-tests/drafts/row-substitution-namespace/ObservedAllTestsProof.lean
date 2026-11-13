module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedAllTestsCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedAllTestsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalQuotientComparisonSyntaxProof InternalOriginalOrderSyntaxProof
open InternalComputabilityApplicationSyntaxProof (programSubst)
open InternalRawListRecursionSyntaxProof (consTermSubst emptySubst)
open InternalAdditionLawsProof (impSubst)
open OriginalClassContextAllPositionObserver OriginalContextInsertion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open ObservedAllTestsDefinitions
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
open InternalTagArithmeticSupportProof (natInduction)
open ObservedAllTestsSyntax ObservedAllTestsCoreProof

theorem allRows (R : Program 2) (count seed candidate parameter : InternalGraphComposition.OTerm alpha) :
 Nonempty (Derivation body Delta (row R count seed candidate parameter)) := by
 let theta : Formula (alpha ⊕ Fin 1) := row R (.var (.inr 0))
   (seed.relabel Sum.inl) (candidate.relabel Sum.inl) (parameter.relabel Sum.inl)
 have hz : Nonempty (Derivation body Delta (instantiate theta (emb z))) := by
   simpa only [theta,instantiate,bindEmbedding,rowSubst,varBind,liftBind] using
     (zeroRow (body := body) (Delta := Delta) R seed candidate parameter)
 have hs : Nonempty (Derivation body (theta :: Delta.map weaken) (successorInstance theta)) := by
   have h := successorRow R (.var (.inr (0 : Fin 1))) (seed.relabel Sum.inl)
     (candidate.relabel Sum.inl) (parameter.relabel Sum.inl)
     (body := body) (Delta := theta :: Delta.map weaken) ⟨Derivation.hypothesis List.mem_cons_self⟩
   simpa only [theta,successorInstance,nextEmbedding,rowSubst,nextLift,nextTerm,Term.subst,Sum.elim_inr] using h
 obtain ⟨hz⟩ := hz
 obtain ⟨hs⟩ := hs
 have h := Derivation.universalElimination (emb count) (natInduction theta hz hs)
 simpa only [theta,instantiate,bindEmbedding,rowSubst,varBind,liftBind] using Nonempty.intro h

theorem actualScan : ObservedAllTestsTargets.ActualScan := by
 intro R body alpha Delta count seed candidate parameter h
 obtain ⟨h⟩ := h
 obtain ⟨hi⟩ := allRows R count seed candidate parameter (body := body) (Delta := Delta)
 exact ⟨Derivation.implicationElimination hi h⟩
theorem actualAllTests : ObservedAllTestsTargets.ActualAllTests := by
 intro R body alpha Delta seed candidate parameter gamma count hg hl hb
 exact OriginalAllPositionRelationTestsProof.testsFromScan R seed candidate parameter gamma count hg hl
   (actualScan R body alpha Delta count seed candidate parameter hb)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedAllTestsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedAllTestsProof
