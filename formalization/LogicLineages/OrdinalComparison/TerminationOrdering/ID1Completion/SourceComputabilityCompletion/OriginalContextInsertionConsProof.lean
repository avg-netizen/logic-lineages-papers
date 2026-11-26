module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionZeroProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionConsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalAcceptanceSupportProof InternalSourceInversionSupportProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalListCodecSupportProof InternalRecursionClosureLogicProof
open InternalGraphCompositionFunctionalityProof InternalPositiveUnfoldingSupportProof
open OriginalContextInsertion OriginalContextInsertionSyntaxProof OriginalContextInsertionLengthProof
open OriginalContextInsertionSupportProof

variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

 theorem consBackward (d cutoff gamma extended head tail extendedTail : OTerm alpha)
    (hc : Nonempty (Derivation body Gamma (consGraph gamma head tail)))
    (he : Nonempty (Derivation body Gamma (consGraph extended head extendedTail)))
    (hi : Nonempty (Derivation body Gamma (Insert d cutoff tail extendedTail))) :
    Nonempty (Derivation body Gamma (Insert d (suc cutoff) gamma extended)) := by
  apply insertCases d cutoff tail extendedTail _ hi
  intro beta j Delta front suffix inserted hj hw
  apply programCases InternalListCodec.consCode
    (Fin.cons (head.relabel j) (Fin.cons front Fin.elim0)) _
  intro beta' k Theta newFront hk hn
  simp only [insertRename,sucRelabel]
  have hc' := renameInto (renameInto hc j Delta hj) k Theta hk
  have he' := renameInto (renameInto he j Delta hj) k Theta hk
  simp only [consGraphRename] at hc' he'
  have hw' := renameInto hw k Theta hk
  rw [witnessesRename] at hw'
  simp only [consTermRename,emptyRename] at hn
  exact insertIntro _ _ _ _ newFront (suffix.relabel k) (inserted.relabel k)
    (andIntro (lengthCons newFront ((head.relabel j).relabel k) (front.relabel k)
      ((cutoff.relabel j).relabel k) hn (andLeft hw'))
      (andIntro (InternalApplicationValidityStackAppendListProof.consBackward
        newFront ((head.relabel j).relabel k) (front.relabel k) (suffix.relabel k)
        ((tail.relabel j).relabel k) ((gamma.relabel j).relabel k)
        hn (andLeft (andRight hw')) hc')
        (andIntro (andLeft (andRight (andRight hw')))
          (InternalApplicationValidityStackAppendListProof.consBackward
            newFront ((head.relabel j).relabel k) (front.relabel k) (inserted.relabel k)
            ((extendedTail.relabel j).relabel k) ((extended.relabel j).relabel k)
            hn (andRight (andRight (andRight hw'))) he'))))

 theorem consForward (d cutoff gamma extended head tail extendedTail : OTerm alpha)
    (hc : Nonempty (Derivation body Gamma (consGraph gamma head tail)))
    (he : Nonempty (Derivation body Gamma (consGraph extended head extendedTail)))
    (hi : Nonempty (Derivation body Gamma (Insert d (suc cutoff) gamma extended))) :
    Nonempty (Derivation body Gamma (Insert d cutoff tail extendedTail)) := by
  apply insertCases d (suc cutoff) gamma extended _ hi
  intro beta j Delta front suffix inserted hj hw
  simp only [sucRelabel] at hw
  apply nonzeroCases front _ (successorLengthNonzero (cutoff.relabel j) front (andLeft hw))
  intro beta' k Theta firstHead rest hk hf
  simp only [insertRename]
  have hc' := renameInto (renameInto hc j Delta hj) k Theta hk
  have he' := renameInto (renameInto he j Delta hj) k Theta hk
  simp only [consGraphRename] at hc' he'
  have hw' := renameInto hw k Theta hk
  simp only [witnessesRename,sucRelabel] at hw'
  exact insertIntro _ _ _ _ rest (suffix.relabel k) (inserted.relabel k)
    (andIntro (successorLengthTail (front.relabel k) firstHead rest
      ((cutoff.relabel j).relabel k) hf (andLeft hw'))
      (andIntro (appendTail (front.relabel k) firstHead rest (suffix.relabel k)
        ((gamma.relabel j).relabel k) ((head.relabel j).relabel k)
        ((tail.relabel j).relabel k) hf hc' (andLeft (andRight hw')))
        (andIntro (andLeft (andRight (andRight hw')))
          (appendTail (front.relabel k) firstHead rest (inserted.relabel k)
            ((extended.relabel j).relabel k) ((head.relabel j).relabel k)
            ((extendedTail.relabel j).relabel k) hf he'
            (andRight (andRight (andRight hw')))))))

 theorem actualOriginalContextInsertionCons :
    OriginalContextInsertionTargets.ActualOriginalContextInsertionCons := by
  intro body alpha d cutoff gamma extended head tail extendedTail
  let A := consGraph gamma head tail ⊓ consGraph extended head extendedTail
  let P := Insert d (suc cutoff) gamma extended
  let Q := Insert d cutoff tail extendedTail
  have ha : Nonempty (Derivation body [P,A] A) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  obtain ⟨hf⟩ := consForward d cutoff gamma extended head tail extendedTail
    (andLeft ha) (andRight ha) ⟨Derivation.hypothesis List.mem_cons_self⟩
  have ha' : Nonempty (Derivation body [Q,A] A) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  obtain ⟨hb⟩ := consBackward d cutoff gamma extended head tail extendedTail
    (andLeft ha') (andRight ha') ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionConsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionConsProof
