module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.SuffixLookupSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteDropProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.SuffixLookupCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn sucRelabel)
open InternalTagArithmeticSupportProof
open InternalAdditionLawsProof (add leftZero leftSuccessor)
open InternalListCodecSupportProof (consGraph consGraphRename)
open InternalApplicationStepPeelSupportProof (andLeft andRight andIntro)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open OriginalContextInsertion (lengthGraph)
open OriginalContextInsertionLengthProof (lengthZeroRecover nonzeroCases)
open OriginalContextInsertionSupportProof (binaryInputs successorLengthNonzero successorLengthTail)
open OriginalTypedDecoderTransportLogicalProof (iffForward iffBackward)
open SuffixLookupSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph InternalRawListRecursion.lookup
  InternalApplicationValidityStackAppend.append OriginalContextInsertion.length

theorem inputsIff (p : Program 2) (out x y x' y' : OTerm alpha)
    (hx : Nonempty (Derivation body Delta (eqn x x')))
    (hy : Nonempty (Derivation body Delta (eqn y y'))) :
    Nonempty (Derivation body Delta ((graph2 p out x y).iff (graph2 p out x' y'))) := by
  let A := graph2 p out x y
  let B := graph2 p out x' y'
  obtain ⟨hf⟩ := binaryInputs p out x y x' y' (withHyp hx A) (withHyp hy A)
    (show Nonempty (Derivation body (A :: Delta) A) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨ex⟩ := hx
  obtain ⟨ey⟩ := hy
  obtain ⟨hb⟩ := binaryInputs p out x' y' x y (withHyp ⟨symm ex⟩ B) (withHyp ⟨symm ey⟩ B)
    (show Nonempty (Derivation body (B :: Delta) B) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

theorem composeIff {P Q T : Formula alpha}
    (hpq : Nonempty (Derivation body Delta (P.iff Q)))
    (hqt : Nonempty (Derivation body Delta (Q.iff T))) :
    Nonempty (Derivation body Delta (P.iff T)) := by
  have hf := iffForward (withHyp hqt P) (iffForward (withHyp hpq P)
    (show Nonempty (Derivation body (P :: Delta) P) from ⟨Derivation.hypothesis List.mem_cons_self⟩))
  have hb := iffBackward (withHyp hpq T) (iffBackward (withHyp hqt T)
    (show Nonempty (Derivation body (T :: Delta) T) from ⟨Derivation.hypothesis List.mem_cons_self⟩))
  obtain ⟨hf⟩ := hf
  obtain ⟨hb⟩ := hb
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

theorem zeroCore (front suffix joined cutoff value : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (fields z front suffix joined))) :
    Nonempty (Derivation body Delta (result z front suffix joined cutoff value)) := by
  have hz := lengthZeroRecover front (andLeft hf)
  have ha := headTransport InternalApplicationValidityStackAppend.append joined front z
    (Fin.cons suffix Fin.elim0) hz (andRight hf)
  have hj := InternalApplicationValidityStackAppendListProof.appendZeroRecover joined suffix ha
  exact inputsIff InternalRawListRecursion.lookup value (add z cutoff) joined cutoff suffix
    ⟨leftZero cutoff⟩ hj

theorem atCons (count front suffix joined cutoff value head tail tailJoined : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (row count)))
    (hf : Nonempty (Derivation body Delta (fields (suc count) front suffix joined)))
    (hc : Nonempty (Derivation body Delta (consGraph front head tail)))
    (ht : Nonempty (Derivation body Delta
      (graph2 InternalApplicationValidityStackAppend.append tailJoined tail suffix))) :
    Nonempty (Derivation body Delta (result (suc count) front suffix joined cutoff value)) := by
  have hl := successorLengthTail front head tail count hc (andLeft hf)
  have htail := rowApply count tail suffix tailJoined cutoff value hi (andIntro hl ht)
  have hjoined := InternalApplicationValidityStackAppendListProof.consForward
    front head tail suffix tailJoined joined hc ht (andRight hf)
  have hlookup := OriginalAllPositionContextDeleteDropProof.lookupConsIff
    joined head tailJoined (add count cutoff) value hjoined
  have hindex := inputsIff (body := body) (Delta := Delta) InternalRawListRecursion.lookup value
    (add (suc count) cutoff) joined (suc (add count cutoff)) joined
    ⟨leftSuccessor count cutoff⟩ ⟨refl joined⟩
  exact composeIff hindex (composeIff hlookup htail)

theorem consQuery (count front suffix joined cutoff value head tail : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (row count)))
    (hf : Nonempty (Derivation body Delta (fields (suc count) front suffix joined)))
    (hc : Nonempty (Derivation body Delta (consGraph front head tail))) :
    Nonempty (Derivation body Delta (result (suc count) front suffix joined cutoff value)) := by
  apply programCases InternalApplicationValidityStackAppend.append
    (Fin.cons tail (Fin.cons suffix Fin.elim0)) _
  intro beta j Theta tailJoined hj ht
  simp only [consTermRename,emptyRename] at ht
  have hi' := renameInto hi j Theta hj
  rw [SuffixLookupSyntaxProof.rowRename] at hi'
  have hf' := renameInto hf j Theta hj
  simp only [fieldsRename,sucRelabel] at hf'
  have hc' := renameInto hc j Theta hj
  rw [consGraphRename] at hc'
  simp only [resultRename,sucRelabel]
  exact atCons (count.relabel j) (front.relabel j) (suffix.relabel j) (joined.relabel j)
    (cutoff.relabel j) (value.relabel j) (head.relabel j) (tail.relabel j) tailJoined hi' hf' hc' ht

theorem successorCore (count front suffix joined cutoff value : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (row count)))
    (hf : Nonempty (Derivation body Delta (fields (suc count) front suffix joined))) :
    Nonempty (Derivation body Delta (result (suc count) front suffix joined cutoff value)) := by
  apply nonzeroCases front _ (successorLengthNonzero count front (andLeft hf))
  intro beta j Theta head tail hj hc
  have hi' := renameInto hi j Theta hj
  rw [SuffixLookupSyntaxProof.rowRename] at hi'
  have hf' := renameInto hf j Theta hj
  simp only [fieldsRename,sucRelabel] at hf'
  simp only [resultRename,sucRelabel]
  exact consQuery (count.relabel j) (front.relabel j) (suffix.relabel j) (joined.relabel j)
    (cutoff.relabel j) (value.relabel j) head tail hi' hf' hc

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.SuffixLookupCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.SuffixLookupCoreProof
