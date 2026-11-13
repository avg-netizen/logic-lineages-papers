module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedInductionCore
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedInductionSyntax
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCoprimeMultipleBoundedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedProof
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
open SourceFramedDefinitions SourceFramedSyntax SourceFramedInductionSyntax

theorem actualBelowCompletion : SourceFramedTargets.ActualBelowCompletion := by
 intro R H M W body alpha Delta c B bound
 let theta : Formula (alpha ⊕ Fin 1) := BelowCompletion R H M W (c.relabel Sum.inl) (B.relabel Sum.inl) (.var (.inr 0))
 have hz : Nonempty (Derivation body Delta (instantiate theta (emb z))) := by
   simpa only [theta,belowInstantiate,liftBind,varBind] using
     SourceFramedInductionCore.zeroRow (body:=body) (Delta:=Delta) R H M W c B
 have hs : Nonempty (Derivation body (theta :: Delta.map weaken) (successorInstance theta)) := by
   have h := SourceFramedInductionCore.succRow (body:=body) (Delta:=theta :: Delta.map weaken)
     R H M W (c.relabel Sum.inl) (B.relabel Sum.inl) (.var (.inr (0 : Fin 1)))
     ⟨Derivation.hypothesis List.mem_cons_self⟩
   simpa only [theta,belowSuccessor,liftNext,varNext] using h
 obtain ⟨hz⟩ := hz
 obtain ⟨hs⟩ := hs
 have h := Derivation.universalElimination (emb bound) (natInduction theta hz hs)
 simpa only [theta,belowInstantiate,liftBind,varBind] using (Nonempty.intro h)

theorem actualSourceFramedCompletion : SourceFramedTargets.ActualSourceFramedCompletion := by
 intro R H M W body alpha Delta c B job hj
 apply programCases OriginalHereditaryFuelProgram.weight (Fin.cons job Fin.elim0) _
 intro beta j Theta weight hi hw
 simp only [consTermRename,emptyRename] at hw
 rw [JobCompletionSyntax.completionRename]
 have hj' := renameInto hj j Theta hi
 rw [jobRename] at hj'
 have hb := actualBelowCompletion R H M W body beta Theta (c.relabel j) (B.relabel j) (suc weight)
 exact belowApply R H M W (c.relabel j) (B.relabel j) (suc weight) (job.relabel j) weight
   hb hj' hw (InternalCoprimeMultipleBoundedProof.selfLtSucc weight)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedProof
