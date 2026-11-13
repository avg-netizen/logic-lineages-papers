module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorComponentsQueries
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorApplicationRootTransferProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorLayerProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsWrapperCongruenceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorApplicationAtCellsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (andLeft andRight andIntro)
open InternalTagArithmeticSupportProof (symm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open EvaluatorConstructorInductionDefinitions EvaluatorConstructorFieldsSyntaxProof
open EvaluatorConstructorCongruenceDefinitions EvaluatorErasureDefinitions
open OriginalHereditaryDeletionRowsCongruenceSyntaxProof (cellRename)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
/-- Close one application AtLength instance after its deletion cells have been
proved. Component outputs and final evaluator witness are actually queried. -/
theorem actual (R : Program 2) (H G : Program 1) (M W : Program 2)
 (compat : UniformRetainedCompatibility R H G M W)
 (count : OTerm alpha) (xs : Fin 16 → OTerm alpha)
 (hf : Nonempty (Derivation body Delta (applicationFields R H G M W count xs)))
 (hc : Nonempty (Derivation body Delta (OriginalHereditaryDeletionRowsCongruence.CellAgreement
   (OriginalHereditaryEvaluatorDefinitions.evaluator R) count (xs 0) (xs 13) (xs 1) (xs 13)))) :
 Nonempty (Derivation body Delta (AdmittedPair R H G M W (xs 0) (xs 1) (xs 13))) := by
 apply EvaluatorConstructorComponentsQueries.actualCases R (xs 0) (xs 1) (xs 13) _
 intro beta j Theta a ar b br row rowr inner out hj ha har hb hbr hrow hrowr hinner hout
 rw [EvaluatorErasureSyntax.admittedRename]
 have hf' := renameInto hf j Theta hj
 rw [applicationRename] at hf'
 have hc' := renameInto hc j Theta hj
 rw [cellRename] at hc'
 have h0 := andLeft hf'
 have h1 := andLeft (andRight hf')
 have hp := andLeft (andRight (andRight (andRight (andRight (andRight (andRight hf')))))))
 have hlen := andRight (andRight (andRight (andRight (andRight (andRight (andRight hf')))))))
 have ea := EvaluatorConstructorApplicationRootTransferProof.retainedRoot R H G M W compat
   (count.relabel j) (fun i => (xs i).relabel j) a ar hf' ha har
 have eb := EvaluatorConstructorApplicationRootTransferProof.evaluatorRoot R H G M W
   (count.relabel j) (fun i => (xs i).relabel j) b br hf' hb hbr
 have hg := pairRight ((xs 13).relabel j) ((xs 14).relabel j) ((xs 15).relabel j) hp
 have er := OriginalHereditaryDeletionRowsWrapperCongruenceProof.exactRowsCongruence
   (OriginalHereditaryEvaluatorDefinitions.evaluator R) body beta Theta
   (count.relabel j) ((xs 0).relabel j) ((xs 13).relabel j) ((xs 15).relabel j)
   ((xs 1).relabel j) ((xs 13).relabel j) ((xs 15).relabel j) row rowr hg hlen hg hlen hc' hrow hrowr
 rw [equalEqn] at ea eb er
 let rightArgs : Fin 2 → OTerm beta := Fin.cons ((xs 1).relabel j) (Fin.cons ((xs 13).relabel j) Fin.elim0)
 have har' := outputTransport (OriginalRootObservation.rootObservation R) ar a rightArgs ⟨symm (Classical.choice ea)⟩ har
 have hbr' := outputTransport (OriginalRootObservation.rootObservation (OriginalHereditaryEvaluatorDefinitions.evaluator R)) br b rightArgs ⟨symm (Classical.choice eb)⟩ hbr
 have hrowr' := outputTransport (OriginalHereditaryDeletionRows.rows (OriginalHereditaryEvaluatorDefinitions.evaluator R)) rowr row rightArgs ⟨symm (Classical.choice er)⟩ hrowr
 have el := EvaluatorConstructorLayerProof.evaluatorAtComponents R H G M W
   ((xs 0).relabel j) ((xs 13).relabel j) a b row inner out h0 ha hb hrow hinner hout
 have eright := EvaluatorConstructorLayerProof.evaluatorAtComponents R H G M W
   ((xs 1).relabel j) ((xs 13).relabel j) a b row inner out h1 har' hbr' hrowr' hinner hout
 exact andIntro h0 (andIntro h1 (EvaluatorErasureSyntax.sameIntro R
   ((xs 0).relabel j) ((xs 1).relabel j) ((xs 13).relabel j) out (andIntro el eright)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorApplicationAtCellsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorApplicationAtCellsProof
