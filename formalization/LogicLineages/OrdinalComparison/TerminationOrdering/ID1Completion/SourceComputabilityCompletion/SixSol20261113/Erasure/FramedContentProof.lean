module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentInductionCore
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentInductionInstances
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCoprimeMultipleBoundedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalAcceptanceSupportProof (programCases)
open InternalControlGraphSupportProof (emptyRename)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalTagArithmeticSyntaxProof (z suc emb liftBind varBind)
open InternalTagArithmeticSupportProof (natInduction)
open InternalTermSubstitutionProof InternalSourceIntroductionSyntaxProof
open InternalBinderTransportProof
open InternalAdditionLawsProof (liftNext varNext)
open OriginalHereditaryInternalAgendaSyntaxProof (jobRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open FramedContentInductionDefinitions FramedContentInductionSyntax FramedContentInductionInstances

theorem actualBelowContent (R : Program 2) (H : Program 1) (M W : Program 2)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (c B bound : OTerm alpha) :
 Nonempty (Derivation body Delta (BelowContent R H M W c B bound)) := by
 let theta : Formula (alpha ⊕ Fin 1) := BelowContent R H M W (c.relabel Sum.inl) (B.relabel Sum.inl) (.var (.inr 0))
 have hz : Nonempty (Derivation body Delta (instantiate theta (emb z))) := by
   simpa only [theta,belowInstantiate,liftBind,varBind] using
     FramedContentInductionBase.zeroRow (body:=body) (Delta:=Delta) R H M W c B
 have hs : Nonempty (Derivation body (theta :: Delta.map weaken) (successorInstance theta)) := by
   have h := FramedContentInductionCore.succRow (body:=body) (Delta:=theta :: Delta.map weaken)
     R H M W (c.relabel Sum.inl) (B.relabel Sum.inl) (.var (.inr (0 : Fin 1)))
     ⟨Derivation.hypothesis List.mem_cons_self⟩
   simpa only [theta,belowSuccessor,liftNext,varNext] using h
 obtain ⟨hz⟩ := hz
 obtain ⟨hs⟩ := hs
 have h := Derivation.universalElimination (emb bound) (natInduction theta hz hs)
 simpa only [theta,belowInstantiate,liftBind,varBind] using (Nonempty.intro h)

theorem actualAllContent (R : Program 2) (H : Program 1) (M W : Program 2)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (c B job : OTerm alpha)
 (hj : Nonempty (Derivation body Delta (OriginalHereditaryInternalAgenda.Job H M W c B job))) :
 Nonempty (Derivation body Delta (FramedContentDefinitions.AllFramedContent R job)) := by
 apply programCases OriginalHereditaryFuelProgram.weight (Fin.cons job Fin.elim0) _
 intro beta j Theta weight hi hw
 simp only [consTermRename,emptyRename] at hw
 rw [FramedContentSyntax.allContentRename]
 have hj' := renameInto hj j Theta hi
 rw [jobRename] at hj'
 have hb := actualBelowContent R H M W body beta Theta (c.relabel j) (B.relabel j) (suc weight)
 exact belowApply R H M W (c.relabel j) (B.relabel j) (suc weight) (job.relabel j) weight
   hb hj' hw (InternalCoprimeMultipleBoundedProof.selfLtSucc weight)
theorem actualFramedContent : FramedContentTargets.ActualFramedContent := by
 intro R H M W body alpha Delta c B job count value hj hf
 exact FramedContentSyntax.contentApply R job count value
   (actualAllContent R H M W body alpha Delta c B job hj) hf
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentProof
