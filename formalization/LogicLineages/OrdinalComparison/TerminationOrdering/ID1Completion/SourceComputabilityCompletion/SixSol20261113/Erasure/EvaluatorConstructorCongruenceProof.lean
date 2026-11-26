module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorInductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorParameterQueries
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorCongruenceProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalRecursionGraphStepSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro)
open GuardedSourceSyntaxProof (numeralRename)
open EvaluatorErasureSyntax (admittedRename)
open EvaluatorConstructorInductionDefinitions
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Exact conditional application endpoint; length and parameter metadata are
queried, and all smaller-context hypotheses are discharged by internal induction. -/
theorem actualApplication : EvaluatorConstructorCongruenceTargets.ActualApplication := by
 intro R H G M W compat body alpha Delta left right fnLeft fnRight argLeft argRight arrow domain codomain fpLeft fpRight apLeft apRight parameter hsL hsR hcL hcR hf ha
 apply EvaluatorConstructorParameterQueries.actualCases parameter _
 intro beta j Theta c gamma count hj hp hlen
 rw [admittedRename]
 have hsL' := renameInto hsL j Theta hj
 have hsR' := renameInto hsR j Theta hj
 have hcL' := renameInto hcL j Theta hj
 have hcR' := renameInto hcR j Theta hj
 have hf' := renameInto hf j Theta hj
 have ha' := renameInto ha j Theta hj
 simp only [graph2Rename,numeralRename] at hsL' hsR'
 simp only [InternalApplicationValidityClosure.applicationConstructors,conjunctionRename,graph2Rename,graph4Rename] at hcL' hcR'
 simp only [admittedRename] at hf' ha'
 let xs : Fin 16 → OTerm beta := ![left.relabel j,right.relabel j,fnLeft.relabel j,fnRight.relabel j,
   argLeft.relabel j,argRight.relabel j,arrow.relabel j,domain.relabel j,codomain.relabel j,
   fpLeft.relabel j,fpRight.relabel j,apLeft.relabel j,apRight.relabel j,parameter.relabel j,c,gamma]
 have fields : Nonempty (Derivation body Theta (applicationFields R H G M W count xs)) :=
   andIntro hsL' (andIntro hsR' (andIntro hcL' (andIntro hcR' (andIntro hf' (andIntro ha' (andIntro hp hlen))))))
 exact EvaluatorConstructorInductionInstancesProof.applicationApply R H G M W count xs
   (EvaluatorConstructorInductionProof.actualAtLength R H G M W compat count) fields
/-- Exact conditional lambda endpoint at its literal extended child parameter.
No parent E equality, canonical fold or native calibration premise is added. -/
theorem actualLambda : EvaluatorConstructorCongruenceTargets.ActualLambda := by
 intro R H G M W compat body alpha Delta left right childLeft childRight domain codomain parameter childParameter c gamma childGamma hsL hsR hp hcons hcp hcL hcR htL htR hchild
 apply programCases OriginalContextInsertion.length (Fin.cons gamma Fin.elim0) _
 intro beta j Theta count hj hlen
 rw [admittedRename]
 simp only [consTermRename,emptyRename] at hlen
 have hsL' := renameInto hsL j Theta hj
 have hsR' := renameInto hsR j Theta hj
 have hp' := renameInto hp j Theta hj
 have hcons' := renameInto hcons j Theta hj
 have hcp' := renameInto hcp j Theta hj
 have hcL' := renameInto hcL j Theta hj
 have hcR' := renameInto hcR j Theta hj
 have htL' := renameInto htL j Theta hj
 have htR' := renameInto htR j Theta hj
 have hchild' := renameInto hchild j Theta hj
 simp only [graph1Rename,graph2Rename,graph3Rename,numeralRename] at hsL' hsR' hp' hcons' hcp' hcL' hcR' htL' htR'
 rw [admittedRename] at hchild'
 let xs : Fin 11 → OTerm beta := ![left.relabel j,right.relabel j,childLeft.relabel j,childRight.relabel j,
   domain.relabel j,codomain.relabel j,parameter.relabel j,childParameter.relabel j,c.relabel j,gamma.relabel j,childGamma.relabel j]
 have fields : Nonempty (Derivation body Theta (lambdaFields R H G M W count xs)) :=
   andIntro hsL' (andIntro hsR' (andIntro hp' (andIntro hcons' (andIntro hcp'
     (andIntro hcL' (andIntro hcR' (andIntro htL' (andIntro htR' (andIntro hchild' hlen)))))))))
 exact EvaluatorConstructorInductionInstancesProof.lambdaApply R H G M W count xs
   (EvaluatorConstructorInductionProof.actualAtLength R H G M W compat count) fields
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorCongruenceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorCongruenceProof
