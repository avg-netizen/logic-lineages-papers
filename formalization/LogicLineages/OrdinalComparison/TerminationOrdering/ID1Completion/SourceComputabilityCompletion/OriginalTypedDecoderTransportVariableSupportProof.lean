module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionBelowProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionVariableAboveProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionVariableTypeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableActionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecDecompositionSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportVariableSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open InternalControlGraphSupportProof InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalOriginalOrderSyntaxProof InternalOriginalOrderProof
open InternalAdditionLawsProof InternalSquareRootArithmeticSupportProof
open InternalBetaTotalityProof InternalRecursionClosureLogicProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalContextInsertion OriginalContextInsertionVariableSupportProof
open OriginalTypedDecoderTransport

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem iffForward {p q : Formula alpha}
    (h : Nonempty (Derivation body Delta (p.iff q)))
    (hp : Nonempty (Derivation body Delta p)) :
    Nonempty (Derivation body Delta q) := by
  obtain ⟨h⟩ := h
  obtain ⟨hp⟩ := hp
  exact ⟨Derivation.implicationElimination (Derivation.conjunctionLeft h) hp⟩

theorem iffBackward {p q : Formula alpha}
    (h : Nonempty (Derivation body Delta (p.iff q)))
    (hq : Nonempty (Derivation body Delta q)) :
    Nonempty (Derivation body Delta p) := by
  obtain ⟨h⟩ := h
  obtain ⟨hq⟩ := hq
  exact ⟨Derivation.implicationElimination (Derivation.conjunctionRight h) hq⟩

/-- Strict arithmetic order rules out the exceptional predecessor-zero case. -/
theorem notLessZero (index : OTerm alpha) :
    Nonempty (Derivation body Delta (Below index z).not) := by
  have h : Nonempty (Derivation body (Below index z :: Delta) (⊥ : Formula alpha)) := by
    apply orderCases _ index z _ ⟨Derivation.hypothesis List.mem_cons_self⟩
    intro beta j Theta gap _ ⟨he⟩
    simp only [zRelabel] at he
    exact ⟨sucNeZeroApply (trans (symm (addSucc (index.relabel j) gap)) he)⟩
  obtain ⟨h⟩ := h
  exact ⟨Derivation.implicationIntroduction h⟩

/-- A genuine predecessor above the cutoff is a successor inverse, and is
not below that cutoff. Both facts hold internally on symbolic arithmetic terms. -/
theorem predecessorAbove (index previous cutoff : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (Below cutoff index)))
    (hp : Nonempty (Derivation body Delta
      (graph1 InternalEqualityTest.predecessor previous index))) :
    Nonempty (Derivation body Delta (eqn index (suc previous))) ∧
      Nonempty (Derivation body Delta (Below previous cutoff).not) := by
  have hn : Nonempty (Derivation body Delta (eqn index z).not) := by
    obtain ⟨hg⟩ := hg
    obtain ⟨hz⟩ := notLessZero (body := body) (Delta := Delta) cutoff
    exact ⟨Derivation.implicationIntroduction
      (Derivation.implicationElimination (addHyp hz _)
        (orderRight cutoff (Derivation.hypothesis List.mem_cons_self) (addHyp hg _)))⟩
  have hs := InternalListCodecDecompositionSupportProof.predecessorAtNonzero index previous hn hp
  have hnext : Nonempty (Derivation body Delta (Below cutoff (suc previous))) := by
    obtain ⟨hs⟩ := hs
    obtain ⟨hg⟩ := hg
    exact ⟨orderRight cutoff hs hg⟩
  have hnot : Nonempty (Derivation body Delta (Below previous cutoff).not) := by
    have hloop := strictWeakTrans (body := body) (Gamma := Below previous cutoff :: Delta)
      previous cutoff previous ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hnext _)
    obtain ⟨hbad⟩ := closedApply (actualOriginalOrderIrreflexivity body alpha previous) hloop
    exact ⟨Derivation.implicationIntroduction hbad⟩
  exact ⟨hs,hnot⟩

theorem shiftBelow (typ index d cutoff gamma extended : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (Insert d cutoff gamma extended)))
    (hb : Nonempty (Derivation body Delta (Below index cutoff)))
    (hv : Nonempty (Derivation body Delta
      (OriginalVariableDecoder.graph (numeral 1) typ index gamma))) :
    Nonempty (Derivation body Delta
      (OriginalVariableDecoder.graph (numeral 1) typ index extended)) :=
  iffForward (OriginalContextInsertionBelowProof.variableBelow
    (numeral 1) typ index d cutoff gamma extended hi hb) hv

theorem shiftAbove (typ index d cutoff gamma extended : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (Insert d cutoff gamma extended)))
    (hn : Nonempty (Derivation body Delta (Below index cutoff).not))
    (hv : Nonempty (Derivation body Delta
      (OriginalVariableDecoder.graph (numeral 1) typ index gamma))) :
    Nonempty (Derivation body Delta
      (OriginalVariableDecoder.graph (numeral 1) typ (suc index) extended)) :=
  iffForward (OriginalContextInsertionVariableAboveProof.variableAbove
    (numeral 1) typ index d cutoff gamma extended hi hn) hv

theorem eraseBelow (typ index d cutoff gamma extended : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (Insert d cutoff gamma extended)))
    (hb : Nonempty (Derivation body Delta (Below index cutoff)))
    (hv : Nonempty (Derivation body Delta
      (OriginalVariableDecoder.graph (numeral 1) typ index extended))) :
    Nonempty (Derivation body Delta
      (OriginalVariableDecoder.graph (numeral 1) typ index gamma)) :=
  iffBackward (OriginalContextInsertionBelowProof.variableBelow
    (numeral 1) typ index d cutoff gamma extended hi hb) hv

/-- At the inserted index the requested type is forced to be the inserted
type. Hence erasure yields bottom at that requested type, without a window. -/
theorem eraseAt (out typ index d cutoff gamma extended : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (Insert d cutoff gamma extended)))
    (he : Nonempty (Derivation body Delta (equal index cutoff)))
    (hv : Nonempty (Derivation body Delta
      (OriginalVariableDecoder.graph (numeral 1) typ index extended)))
    (ho : Nonempty (Derivation body Delta (graph1 bottomConstructor out d))) :
    Nonempty (Derivation body Delta (graph1 bottomConstructor out typ)) := by
  rw [equalEqn] at he
  have hv' := variableInputs (numeral 1) typ index extended cutoff extended he ⟨refl extended⟩ hv
  obtain ⟨ht⟩ := OriginalContextInsertionVariableTypeProof.acceptedType
    typ d cutoff gamma extended hi hv'
  exact headTransport bottomConstructor out d typ Fin.elim0 ⟨symm ht⟩ ho

theorem eraseAbove (typ index previous d cutoff gamma extended : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (Insert d cutoff gamma extended)))
    (hg : Nonempty (Derivation body Delta (Below cutoff index)))
    (hp : Nonempty (Derivation body Delta
      (graph1 InternalEqualityTest.predecessor previous index)))
    (hv : Nonempty (Derivation body Delta
      (OriginalVariableDecoder.graph (numeral 1) typ index extended))) :
    Nonempty (Derivation body Delta
      (OriginalVariableDecoder.graph (numeral 1) typ previous gamma)) := by
  obtain ⟨hs,hn⟩ := predecessorAbove index previous cutoff hg hp
  have hv' := variableInputs (numeral 1) typ index extended (suc previous) extended hs ⟨refl extended⟩ hv
  exact iffBackward (OriginalContextInsertionVariableAboveProof.variableAbove
    (numeral 1) typ previous d cutoff gamma extended hi hn) hv'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportVariableSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportVariableSupportProof
