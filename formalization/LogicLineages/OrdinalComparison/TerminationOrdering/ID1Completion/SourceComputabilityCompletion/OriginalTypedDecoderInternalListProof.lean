module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalScalarProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalListProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalAcceptanceSupportProof
open OriginalLambdaConstructorGraphSyntaxProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalTypedDecoder OriginalTypedDecoderStepSpecification
open OriginalTypedDecoderInternalScalarSyntaxProof OriginalTypedDecoderInternalScalarProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem listHead (code head tail : OTerm alpha)
    (h : Nonempty (Derivation body Delta (StepArrowFields code head tail))) :
    Nonempty (Derivation body Delta (graph1 InternalListCodec.headCode head code)) := by
  apply stepArrowFieldsCases code head tail _ h
  intro beta j Theta previous hj hp hpair
  rw [graph1Rename]
  exact unaryValue InternalUnpair.left InternalEqualityTest.predecessor
    (head.relabel j) previous (Fin.cons (code.relabel j) Fin.elim0)
    (pairLeft previous (head.relabel j) (tail.relabel j) hpair) hp

theorem listTail (code head tail : OTerm alpha)
    (h : Nonempty (Derivation body Delta (StepArrowFields code head tail))) :
    Nonempty (Derivation body Delta (graph1 InternalListCodec.tailCode tail code)) := by
  apply stepArrowFieldsCases code head tail _ h
  intro beta j Theta previous hj hp hpair
  rw [graph1Rename]
  exact unaryValue InternalUnpair.right InternalEqualityTest.predecessor
    (tail.relabel j) previous (Fin.cons (code.relabel j) Fin.elim0)
    (pairRight previous (head.relabel j) (tail.relabel j) hpair) hp

theorem consArrowFields (code head tail : OTerm alpha)
    (h : Nonempty (Derivation body Delta (StepCons code head tail))) :
    Nonempty (Derivation body Delta (StepArrowFields code head tail)) := by
  have hd := InternalListCodecSupportProof.consDestruction code head tail h
  have hh := andLeft hd
  have ht := andLeft (andRight hd)
  apply programCases InternalEqualityTest.predecessor (Fin.cons code Fin.elim0) _
  intro beta j Theta previous hj hp
  rw [stepArrowFieldsRename]
  have hh' := renameInto hh j Theta hj
  have ht' := renameInto ht j Theta hj
  simp only [programRename,consTermRename,emptyRename] at hh' ht' hp
  let xx : Fin 1 → OTerm beta := Fin.cons (code.relabel j) Fin.elim0
  have hl := unaryRecover InternalUnpair.left InternalEqualityTest.predecessor
    (head.relabel j) previous xx hh' hp
  have hr := unaryRecover InternalUnpair.right InternalEqualityTest.predecessor
    (tail.relabel j) previous xx ht' hp
  exact stepArrowFieldsIntro _ _ _ previous hp
    (reconstructPair previous (head.relabel j) (tail.relabel j) hl hr)

theorem consNonzero (code head tail : OTerm alpha)
    (h : Nonempty (Derivation body Delta (StepCons code head tail))) :
    Nonempty (Derivation body Delta (equal code (numeral 0)).not) := by
  have hn := andRight (andRight (InternalListCodecSupportProof.consDestruction code head tail h))
  simpa only [equalEqn,numeral] using hn

theorem consFields (code head tail : OTerm alpha)
    (hn : Nonempty (Derivation body Delta (equal code (numeral 0)).not))
    (hf : Nonempty (Derivation body Delta (StepArrowFields code head tail))) :
    Nonempty (Derivation body Delta (StepCons code head tail)) := by
  apply InternalListCodecDecompositionSupportProof.reconstructNonzero code head tail
  · simpa only [equalEqn,numeral] using hn
  · exact listHead code head tail hf
  · exact listTail code head tail hf

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalListProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalListProof
