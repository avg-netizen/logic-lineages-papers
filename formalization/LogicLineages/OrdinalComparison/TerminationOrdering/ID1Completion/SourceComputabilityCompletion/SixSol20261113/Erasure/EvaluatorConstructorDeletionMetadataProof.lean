module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteInductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteLengthProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCoprimeMultipleBoundedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorDeletionMetadataProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeelSupportProof (andIntro)
open InternalTagArithmeticSyntaxProof (suc)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
/-- Actual in-range lookup/deletion facts pay both insertion geometry and the
strictly smaller context-length induction index. No decoded list is used. -/
theorem atSuccessor (count gamma cutoff deleted d : OTerm alpha)
 (hl : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph (suc count) gamma)))
 (hb : Nonempty (Derivation body Delta (OriginalContextInsertion.Below cutoff (suc count))))
 (hd : Nonempty (Derivation body Delta (graph2 OriginalClassContextAllPositionObserver.deleteAt deleted cutoff gamma)))
 (hk : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup d cutoff gamma))) :
 Nonempty (Derivation body Delta (OriginalContextInsertion.Insert d cutoff deleted gamma)) ∧
 Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph count deleted)) ∧
 Nonempty (Derivation body Delta (InternalLessThan.strictLess count (suc count))) := by
 have hi := OriginalAllPositionContextDeleteInductionProof.actualDeletionInsertion
   body alpha Delta (suc count) gamma cutoff deleted d
 have hp := andIntro hl (andIntro hb (andIntro hd hk))
 refine ⟨⟨Derivation.implicationElimination (Classical.choice hi) (Classical.choice hp)⟩, ?_, ?_⟩
 · exact OriginalAllPositionContextDeleteLengthProof.deleteLength gamma count cutoff deleted hl hb hd
 · exact InternalCoprimeMultipleBoundedProof.selfLtSucc count
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorDeletionMetadataProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorDeletionMetadataProof
