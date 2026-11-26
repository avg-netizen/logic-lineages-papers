module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionLengthProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalAcceptanceSupportProof InternalSourceInversionSupportProof
open InternalControlGraphSupportProof InternalRawListRecursionSyntaxProof
open InternalRawListRecursionSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalListCodecSupportProof InternalListCodecDecompositionSupportProof
open InternalRecursionClosureLogicProof InternalGraphCompositionFunctionalityProof
open InternalPositiveUnfoldingSupportProof InternalBetaTotalityProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalContextInsertion OriginalContextInsertionSyntaxProof OriginalContextInsertionLengthProof

variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

 theorem binaryInputs (p : Program 2) (out x y x' y' : OTerm alpha)
    (hx : Nonempty (Derivation body Gamma (eqn x x')))
    (hy : Nonempty (Derivation body Gamma (eqn y y')))
    (h : Nonempty (Derivation body Gamma (graph2 p out x y))) :
    Nonempty (Derivation body Gamma (graph2 p out x' y')) := by
  apply InternalGraphCompositionEqualityProof.graphInputTransport body alpha 2 Gamma _ out
    (Fin.cons x (Fin.cons y Fin.elim0)) (Fin.cons x' (Fin.cons y' Fin.elim0)) _ h
  intro i
  refine Fin.cases ?_ (Fin.cases ?_ (fun q => Fin.elim0 q)) i
  · rw [InternalSourceInversionSupportProof.onEquality]
    exact hx
  · rw [InternalSourceInversionSupportProof.onEquality]
    exact hy

 theorem successorLengthNonzero (cutoff front : OTerm alpha)
    (hl : Nonempty (Derivation body Gamma (lengthGraph (suc cutoff) front))) :
    Nonempty (Derivation body Gamma (eqn front z).not) := by
  obtain ⟨hl⟩ := hl
  have hz : Nonempty (Derivation body (eqn front z :: Gamma) (lengthGraph (suc cutoff) z)) :=
    headTransport length (suc cutoff) front z Fin.elim0
      ⟨Derivation.hypothesis List.mem_cons_self⟩ ⟨addHyp hl _⟩
  obtain ⟨he⟩ := lengthNilRecover (suc cutoff) hz
  exact ⟨Derivation.implicationIntroduction (sucNeZeroApply he)⟩

 theorem successorLengthTail (front head tail cutoff : OTerm alpha)
    (hc : Nonempty (Derivation body Gamma (consGraph front head tail)))
    (hl : Nonempty (Derivation body Gamma (lengthGraph (suc cutoff) front))) :
    Nonempty (Derivation body Gamma (lengthGraph cutoff tail)) := by
  apply programCases length (Fin.cons tail Fin.elim0) _
  intro beta j Delta count hj ht
  rw [lengthRename]
  have hc' := renameInto hc j Delta hj
  rw [consGraphRename] at hc'
  have hl' := renameInto hl j Delta hj
  simp only [lengthRename,sucRelabel] at hl'
  simp only [consTermRename,emptyRename] at ht
  obtain ⟨he⟩ := lengthConsRecover (front.relabel j) (head.relabel j)
    (tail.relabel j) (suc (cutoff.relabel j)) count hc' hl' ht
  exact outputTransport length count (cutoff.relabel j) (Fin.cons (tail.relabel j) Fin.elim0)
    ⟨symm (cancelSuc he)⟩ ht

/-- Invert an append through both original constructors. The two heads need
not be supplied equal: original destructor functionality fixes the tail. -/
 theorem appendTail (front firstHead rest suffix joined secondHead tail : OTerm alpha)
    (hf : Nonempty (Derivation body Gamma (consGraph front firstHead rest)))
    (hj : Nonempty (Derivation body Gamma (consGraph joined secondHead tail)))
    (ha : Nonempty (Derivation body Gamma
      (graph2 InternalApplicationValidityStackAppend.append joined front suffix))) :
    Nonempty (Derivation body Gamma
      (graph2 InternalApplicationValidityStackAppend.append tail rest suffix)) := by
  apply programCases InternalApplicationValidityStackAppend.append
    (Fin.cons rest (Fin.cons suffix Fin.elim0)) _
  intro beta j Delta result hk hr
  rw [graph2Rename]
  have hf' := renameInto hf j Delta hk
  have hj' := renameInto hj j Delta hk
  have ha' := renameInto ha j Delta hk
  simp only [consGraphRename,graph2Rename] at hf' hj' ha'
  simp only [consTermRename,emptyRename] at hr
  have hc := InternalApplicationValidityStackAppendListProof.consForward
    (front.relabel j) (firstHead.relabel j) (rest.relabel j) (suffix.relabel j)
    result (joined.relabel j) hf' hr ha'
  have he := valueUnique InternalListCodec.tailCode result (tail.relabel j)
    (Fin.cons (joined.relabel j) Fin.elim0)
    (consTail (joined.relabel j) (firstHead.relabel j) result hc)
    (consTail (joined.relabel j) (secondHead.relabel j) (tail.relabel j) hj')
  exact outputTransport InternalApplicationValidityStackAppend.append result (tail.relabel j)
    (Fin.cons (rest.relabel j) (Fin.cons (suffix.relabel j) Fin.elim0)) he hr

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSupportProof
