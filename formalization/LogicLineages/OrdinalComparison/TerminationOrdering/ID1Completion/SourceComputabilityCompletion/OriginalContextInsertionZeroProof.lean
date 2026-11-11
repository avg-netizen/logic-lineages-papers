module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionZeroProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalListCodecSupportProof InternalRecursionClosureLogicProof
open InternalGraphCompositionFunctionalityProof
open InternalApplicationValidityStackAppendListProof
open OriginalContextInsertion OriginalContextInsertionSyntaxProof OriginalContextInsertionLengthProof
open OriginalContextInsertionSupportProof

variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

 theorem zeroForward (d gamma extended : OTerm alpha)
    (h : Nonempty (Derivation body Gamma (Insert d z gamma extended))) :
    Nonempty (Derivation body Gamma (consGraph extended d gamma)) := by
  apply insertCases d z gamma extended _ h
  intro beta j Delta front suffix inserted hj hw
  rw [consGraphRename]
  simp only [zRelabel] at hw
  have hp := lengthZeroRecover front (andLeft hw)
  have ha := headTransport InternalApplicationValidityStackAppend.append (gamma.relabel j)
    front z (Fin.cons suffix Fin.elim0) hp (andLeft (andRight hw))
  have hb := headTransport InternalApplicationValidityStackAppend.append (extended.relabel j)
    front z (Fin.cons inserted Fin.elim0) hp (andRight (andRight (andRight hw)))
  obtain ⟨hg⟩ := appendZeroRecover (gamma.relabel j) suffix ha
  obtain ⟨he⟩ := appendZeroRecover (extended.relabel j) inserted hb
  have hc := binaryInputs InternalListCodec.consCode inserted (d.relabel j) suffix
    (d.relabel j) (gamma.relabel j) ⟨refl _⟩ ⟨symm hg⟩
    (andLeft (andRight (andRight hw)))
  exact outputTransport InternalListCodec.consCode inserted (extended.relabel j)
    (Fin.cons (d.relabel j) (Fin.cons (gamma.relabel j) Fin.elim0)) ⟨symm he⟩ hc

 theorem zeroBackward (d gamma extended : OTerm alpha)
    (h : Nonempty (Derivation body Gamma (consGraph extended d gamma))) :
    Nonempty (Derivation body Gamma (Insert d z gamma extended)) :=
  insertIntro d z gamma extended z gamma extended
    (andIntro lengthZero (andIntro (appendZeroValue gamma)
      (andIntro h (appendZeroValue extended))))

 theorem actualOriginalContextInsertionZero :
    OriginalContextInsertionTargets.ActualOriginalContextInsertionZero := by
  intro body alpha d gamma extended
  obtain ⟨hf⟩ := zeroForward (body := body) (Gamma := [Insert d z gamma extended])
    d gamma extended ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := zeroBackward (body := body) (Gamma := [consGraph extended d gamma])
    d gamma extended ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionZeroProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionZeroProof
