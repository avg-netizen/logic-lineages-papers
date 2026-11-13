module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankMemoRecurrenceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankMemoSuccessorProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (suc sucRelabel)
open InternalApplicationStepPeelSupportProof (andLeft)
open RankMemoDefinitions
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem atCons (stage old value next : OTerm alpha)
 (ht : Nonempty (Derivation body Delta (graph1 table old stage)))
 (hv : Nonempty (Derivation body Delta (graph2 nextValue value stage old)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode next value old))) :
 Nonempty (Derivation body Delta (graph1 decoder value (suc stage))) :=
 unaryValue InternalListCodec.headCode table value next (Fin.cons (suc stage) Fin.elim0)
   (andLeft (InternalListCodecSupportProof.consDestruction next value old hc))
   (RankMemoRecurrenceProof.actualNext body alpha Delta stage old value next ht hv hc)

theorem atSuccessor (stage old value : OTerm alpha)
 (ht : Nonempty (Derivation body Delta (graph1 table old stage)))
 (hv : Nonempty (Derivation body Delta (graph2 nextValue value stage old))) :
 Nonempty (Derivation body Delta (graph1 decoder value (suc stage))) := by
 apply programCases InternalListCodec.consCode (Fin.cons value (Fin.cons old Fin.elim0)) _
 intro beta j Theta next hj hc
 simp only [graph1Rename,sucRelabel]
 simp only [consTermRename,emptyRename] at hc
 have ht' := renameInto ht j Theta hj
 have hv' := renameInto hv j Theta hj
 rw [graph1Rename] at ht'
 rw [graph2Rename] at hv'
 exact atCons (stage.relabel j) (old.relabel j) (value.relabel j) next ht' hv' hc
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankMemoSuccessorProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankMemoSuccessorProof
