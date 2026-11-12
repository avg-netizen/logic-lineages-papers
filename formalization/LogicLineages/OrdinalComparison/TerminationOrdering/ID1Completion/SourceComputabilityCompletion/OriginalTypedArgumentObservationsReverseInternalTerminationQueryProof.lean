module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalTerminationCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalTerminationQueryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open OriginalTypedArgumentObservations
open OriginalTypedArgumentObservationsReverseInternalTerminationDefinitions OriginalTypedArgumentObservationsReverseInternalTerminationSyntaxProof OriginalTypedArgumentObservationsReverseInternalTerminationCoreProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem consAt3 (raw state acc out head tail nextAcc next middle : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw raw)))
 (hf : Nonempty (Derivation body Delta (fields raw state acc out)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
 (ha : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode nextAcc head acc)))
 (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing next tail nextAcc)))
 (hm : Nonempty (Derivation body Delta (graph2 reverseRun middle (suc tail) next)))
 : Nonempty (Derivation body Delta (graph1 InternalUnpair.left z out)) := by
  apply programCases InternalUnpair.right ![middle] _
  intro beta rho Theta result hrho hresult
  simp only [graph1Rename,zRelabel]
  have hi' := renameInto hi rho Theta hrho
  simp only [belowRawRename] at hi'
  have hf' := renameInto hf rho Theta hrho
  simp only [fields,conjunctionRename,graph2Rename,sucRelabel] at hf'
  have hc' := renameInto hc rho Theta hrho
  simp only [graph2Rename,sucRelabel] at hc'
  have ha' := renameInto ha rho Theta hrho
  simp only [graph2Rename,sucRelabel] at ha'
  have hn' := renameInto hn rho Theta hrho
  simp only [graph2Rename,sucRelabel] at hn'
  have hm' := renameInto hm rho Theta hrho
  simp only [graph2Rename,sucRelabel] at hm'
  exact consValues (raw.relabel rho) (state.relabel rho) (acc.relabel rho) (out.relabel rho) (head.relabel rho) (tail.relabel rho) (nextAcc.relabel rho) (next.relabel rho) (middle.relabel rho) result hi' hf' hc' ha' hn' hm' hresult

theorem consAt2 (raw state acc out head tail nextAcc next : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw raw)))
 (hf : Nonempty (Derivation body Delta (fields raw state acc out)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
 (ha : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode nextAcc head acc)))
 (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing next tail nextAcc)))
 : Nonempty (Derivation body Delta (graph1 InternalUnpair.left z out)) := by
  apply programCases reverseRun ![suc tail,next] _
  intro beta rho Theta middle hrho hm
  simp only [graph1Rename,zRelabel]
  have hi' := renameInto hi rho Theta hrho
  simp only [belowRawRename] at hi'
  have hf' := renameInto hf rho Theta hrho
  simp only [fields,conjunctionRename,graph2Rename,sucRelabel] at hf'
  have hc' := renameInto hc rho Theta hrho
  simp only [graph2Rename,sucRelabel] at hc'
  have ha' := renameInto ha rho Theta hrho
  simp only [graph2Rename,sucRelabel] at ha'
  have hn' := renameInto hn rho Theta hrho
  simp only [graph2Rename,sucRelabel] at hn'
  simp only [sucRelabel] at hm
  exact consAt3 (raw.relabel rho) (state.relabel rho) (acc.relabel rho) (out.relabel rho) (head.relabel rho) (tail.relabel rho) (nextAcc.relabel rho) (next.relabel rho) middle hi' hf' hc' ha' hn' hm

theorem consAt1 (raw state acc out head tail nextAcc : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw raw)))
 (hf : Nonempty (Derivation body Delta (fields raw state acc out)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
 (ha : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode nextAcc head acc)))
 : Nonempty (Derivation body Delta (graph1 InternalUnpair.left z out)) := by
  apply programCases InternalPairing.pairing ![tail,nextAcc] _
  intro beta rho Theta next hrho hn
  simp only [graph1Rename,zRelabel]
  have hi' := renameInto hi rho Theta hrho
  simp only [belowRawRename] at hi'
  have hf' := renameInto hf rho Theta hrho
  simp only [fields,conjunctionRename,graph2Rename,sucRelabel] at hf'
  have hc' := renameInto hc rho Theta hrho
  simp only [graph2Rename,sucRelabel] at hc'
  have ha' := renameInto ha rho Theta hrho
  simp only [graph2Rename,sucRelabel] at ha'
  exact consAt2 (raw.relabel rho) (state.relabel rho) (acc.relabel rho) (out.relabel rho) (head.relabel rho) (tail.relabel rho) (nextAcc.relabel rho) next hi' hf' hc' ha' hn

theorem consAt0 (raw state acc out head tail : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw raw)))
 (hf : Nonempty (Derivation body Delta (fields raw state acc out)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
 : Nonempty (Derivation body Delta (graph1 InternalUnpair.left z out)) := by
  apply programCases InternalListCodec.consCode ![head,acc] _
  intro beta rho Theta nextAcc hrho ha
  simp only [graph1Rename,zRelabel]
  have hi' := renameInto hi rho Theta hrho
  simp only [belowRawRename] at hi'
  have hf' := renameInto hf rho Theta hrho
  simp only [fields,conjunctionRename,graph2Rename,sucRelabel] at hf'
  have hc' := renameInto hc rho Theta hrho
  simp only [graph2Rename,sucRelabel] at hc'
  exact consAt1 (raw.relabel rho) (state.relabel rho) (acc.relabel rho) (out.relabel rho) (head.relabel rho) (tail.relabel rho) nextAcc hi' hf' hc' ha

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalTerminationQueryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalTerminationQueryProof
