module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalAccumulatorBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalAccumulatorConsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextTwoDeletionCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendListProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalQuerySyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalAccumulatorCoreProof
open OriginalTypedArgumentObservationsReverseInternalQuerySyntaxProof (unaryVectorRename binaryVectorRename)
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendListProof
open OriginalContextTwoDeletionCoreProof (secondInput)
open OriginalTypedArgumentObservationsReverseInternalAccumulatorDefinitions OriginalTypedArgumentObservationsReverseInternalAccumulatorBindingProof OriginalTypedArgumentObservationsReverseInternalAccumulatorConsProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem zeroValues (value singleton combined acc left right nextAcc : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (fields z value singleton combined acc left right)))
 (ha : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode nextAcc value acc))) :
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode right value left)) := by
 have he := appendZeroRecover combined singleton (andLeft (andRight hf))
 obtain ⟨he⟩ := he
 have hc := outputTransport InternalListCodec.consCode singleton combined ![value,z] ⟨symm he⟩ (andLeft hf)
 have hr := consValue combined value z acc nextAcc nextAcc hc ha (zero nextAcc)
 have hleft := valueUnique accumulated acc left ![z,acc] (zero acc) (andLeft (andRight (andRight hf)))
 have hright := valueUnique accumulated nextAcc right ![combined,acc] hr (andRight (andRight (andRight hf)))
 exact secondInput InternalListCodec.consCode right value acc left hleft
   (outputTransport InternalListCodec.consCode nextAcc right ![value,acc] hright ha)

theorem zeroCore (value singleton combined acc left right : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (fields z value singleton combined acc left right))) :
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode right value left)) := by
 apply programCases InternalListCodec.consCode ![value,acc] _
 intro beta rho Theta nextAcc hrho ha
 rw [binaryVectorRename] at ha
 simp only [graph2Rename]
 have hf' := renameInto hf rho Theta hrho
 simp only [fields,conjunctionRename,graph2Rename,zRelabel] at hf'
 exact zeroValues (value.relabel rho) (singleton.relabel rho) (combined.relabel rho)
   (acc.relabel rho) (left.relabel rho) (right.relabel rho) nextAcc hf' ha

theorem consValues (front value singleton combined acc left right head tail joined nextAcc tailLeft tailRight : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw front)))
 (hf : Nonempty (Derivation body Delta (fields front value singleton combined acc left right)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode front head tail)))
 (hj : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append joined tail singleton)))
 (ha : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode nextAcc head acc)))
 (hl : Nonempty (Derivation body Delta (graph2 accumulated tailLeft tail nextAcc)))
 (hr : Nonempty (Derivation body Delta (graph2 accumulated tailRight joined nextAcc))) :
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode right value left)) := by
 have hb := InternalListCodecDecompositionSupportProof.consTailDescent front head tail hc
 have ih := belowRawApply front tail value singleton joined nextAcc tailLeft tailRight hi hb
   (andIntro (andLeft hf) (andIntro hj (andIntro hl hr)))
 have hjoined := consForward front head tail singleton joined combined hc hj (andLeft (andRight hf))
 have hlo := consValue front head tail acc nextAcc tailLeft hc ha hl
 have hro := consValue combined head joined acc nextAcc tailRight hjoined ha hr
 have el := valueUnique accumulated tailLeft left ![front,acc] hlo (andLeft (andRight (andRight hf)))
 have er := valueUnique accumulated tailRight right ![combined,acc] hro (andRight (andRight (andRight hf)))
 exact secondInput InternalListCodec.consCode right value tailLeft left el
   (outputTransport InternalListCodec.consCode tailRight right ![value,tailLeft] er ih)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalAccumulatorCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalAccumulatorCoreProof
