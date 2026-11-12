module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalAccumulatorCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalAccumulatorQueryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z zRelabel)
open OriginalTypedArgumentObservationsReverseInternalAccumulatorDefinitions OriginalTypedArgumentObservationsReverseInternalAccumulatorSyntaxProof OriginalTypedArgumentObservationsReverseInternalAccumulatorCoreProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem consAt3 (front value singleton combined acc left right head tail joined nextAcc tailLeft : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw front)))
 (hf : Nonempty (Derivation body Delta (fields front value singleton combined acc left right)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode front head tail)))
 (hj : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append joined tail singleton)))
 (ha : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode nextAcc head acc)))
 (hl : Nonempty (Derivation body Delta (graph2 accumulated tailLeft tail nextAcc)))
 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode right value left)) := by
  apply programCases accumulated ![joined,nextAcc] _
  intro beta rho Theta tailRight hrho hr
  simp only [graph2Rename]
  have hi' := renameInto hi rho Theta hrho
  simp only [belowRawRename] at hi'
  have hf' := renameInto hf rho Theta hrho
  simp only [fields,conjunctionRename,graph2Rename,zRelabel] at hf'
  have hc' := renameInto hc rho Theta hrho
  simp only [graph2Rename] at hc'
  have hj' := renameInto hj rho Theta hrho
  simp only [graph2Rename] at hj'
  have ha' := renameInto ha rho Theta hrho
  simp only [graph2Rename] at ha'
  have hl' := renameInto hl rho Theta hrho
  simp only [graph2Rename] at hl'
  exact consValues (front.relabel rho) (value.relabel rho) (singleton.relabel rho) (combined.relabel rho) (acc.relabel rho) (left.relabel rho) (right.relabel rho) (head.relabel rho) (tail.relabel rho) (joined.relabel rho) (nextAcc.relabel rho) (tailLeft.relabel rho) tailRight hi' hf' hc' hj' ha' hl' hr

theorem consAt2 (front value singleton combined acc left right head tail joined nextAcc : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw front)))
 (hf : Nonempty (Derivation body Delta (fields front value singleton combined acc left right)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode front head tail)))
 (hj : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append joined tail singleton)))
 (ha : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode nextAcc head acc)))
 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode right value left)) := by
  apply programCases accumulated ![tail,nextAcc] _
  intro beta rho Theta tailLeft hrho hl
  simp only [graph2Rename]
  have hi' := renameInto hi rho Theta hrho
  simp only [belowRawRename] at hi'
  have hf' := renameInto hf rho Theta hrho
  simp only [fields,conjunctionRename,graph2Rename,zRelabel] at hf'
  have hc' := renameInto hc rho Theta hrho
  simp only [graph2Rename] at hc'
  have hj' := renameInto hj rho Theta hrho
  simp only [graph2Rename] at hj'
  have ha' := renameInto ha rho Theta hrho
  simp only [graph2Rename] at ha'
  exact consAt3 (front.relabel rho) (value.relabel rho) (singleton.relabel rho) (combined.relabel rho) (acc.relabel rho) (left.relabel rho) (right.relabel rho) (head.relabel rho) (tail.relabel rho) (joined.relabel rho) (nextAcc.relabel rho) tailLeft hi' hf' hc' hj' ha' hl

theorem consAt1 (front value singleton combined acc left right head tail joined : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw front)))
 (hf : Nonempty (Derivation body Delta (fields front value singleton combined acc left right)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode front head tail)))
 (hj : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append joined tail singleton)))
 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode right value left)) := by
  apply programCases InternalListCodec.consCode ![head,acc] _
  intro beta rho Theta nextAcc hrho ha
  simp only [graph2Rename]
  have hi' := renameInto hi rho Theta hrho
  simp only [belowRawRename] at hi'
  have hf' := renameInto hf rho Theta hrho
  simp only [fields,conjunctionRename,graph2Rename,zRelabel] at hf'
  have hc' := renameInto hc rho Theta hrho
  simp only [graph2Rename] at hc'
  have hj' := renameInto hj rho Theta hrho
  simp only [graph2Rename] at hj'
  exact consAt2 (front.relabel rho) (value.relabel rho) (singleton.relabel rho) (combined.relabel rho) (acc.relabel rho) (left.relabel rho) (right.relabel rho) (head.relabel rho) (tail.relabel rho) (joined.relabel rho) nextAcc hi' hf' hc' hj' ha

theorem consAt0 (front value singleton combined acc left right head tail : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw front)))
 (hf : Nonempty (Derivation body Delta (fields front value singleton combined acc left right)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode front head tail)))
 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode right value left)) := by
  apply programCases InternalApplicationValidityStackAppend.append ![tail,singleton] _
  intro beta rho Theta joined hrho hj
  simp only [graph2Rename]
  have hi' := renameInto hi rho Theta hrho
  simp only [belowRawRename] at hi'
  have hf' := renameInto hf rho Theta hrho
  simp only [fields,conjunctionRename,graph2Rename,zRelabel] at hf'
  have hc' := renameInto hc rho Theta hrho
  simp only [graph2Rename] at hc'
  exact consAt1 (front.relabel rho) (value.relabel rho) (singleton.relabel rho) (combined.relabel rho) (acc.relabel rho) (left.relabel rho) (right.relabel rho) (head.relabel rho) (tail.relabel rho) joined hi' hf' hc' hj

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalAccumulatorQueryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalAccumulatorQueryProof
