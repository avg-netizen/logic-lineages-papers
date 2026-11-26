module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankMemoRecurrenceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankMemoCoherenceSyntax
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankMemoTableTailProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRawListRecursionSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open RankMemoDefinitions
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem tableTail (old out index : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph1 table old index)))
 (hs : Nonempty (Derivation body Delta (graph1 table out (suc index)))) :
 Nonempty (Derivation body Delta (graph1 InternalListCodec.tailCode old out)) := by
 have ht := recursionRecover tableBase tableStep out old index Fin.elim0 hp hs
 apply programCases nextValue (Fin.cons index (Fin.cons old Fin.elim0)) _
 intro beta j Theta value hj hv
 rw [graph1Rename]
 simp only [consTermRename,emptyRename] at hv
 have ht' := renameInto ht j Theta hj
 simp only [programRename,consTermRename,emptyRename] at ht'
 have hc := binaryRecover InternalListCodec.consCode nextValue (.projection 1)
   (out.relabel j) value (old.relabel j)
   (Fin.cons (index.relabel j) (Fin.cons (old.relabel j) Fin.elim0)) ht' hv
   (projectionValue 1 (Fin.cons (index.relabel j) (Fin.cons (old.relabel j) Fin.elim0)))
 exact andLeft (andRight (InternalListCodecSupportProof.consDestruction (out.relabel j) value (old.relabel j) hc))

theorem decoderHead (out code tab : OTerm alpha)
 (hr : Nonempty (Derivation body Delta (graph1 decoder out code)))
 (ht : Nonempty (Derivation body Delta (graph1 table tab code))) :
 Nonempty (Derivation body Delta (graph1 InternalListCodec.headCode out tab)) :=
 unaryRecover InternalListCodec.headCode table out tab (Fin.cons code Fin.elim0) hr ht
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankMemoTableTailProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankMemoTableTailProof
