module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankTransportInductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankTransportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof (refl symm trans congSuc)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternal OriginalRawVariableRank
open OriginalRawVariableRankTransport
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
open OriginalRawVariableRankTransportBindingProof OriginalRawVariableRankTransportInductionProof
open OriginalRawVariableRankTransportArithmeticProof
open OriginalRawSyntaxTransportInternalInterfaceSupportProof

theorem rankShiftEqual (raw shifted before after k : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph2 shiftRaw shifted k raw)))
    (hb : Nonempty (Derivation body Delta (graph1 variableRankRaw before raw)))
    (ha : Nonempty (Derivation body Delta (graph1 variableRankRaw after shifted))) :
    Nonempty (Derivation body Delta (equal after before)) :=
  atRawApply (fold .shift) false raw z k shifted before after (allRawTransport false raw)
    (zeroFirstForward (fold .shift) shifted k raw hs) hb ha

theorem rankShiftForward (raw shifted rank k : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph2 shiftRaw shifted k raw)))
    (hr : Nonempty (Derivation body Delta (graph1 variableRankRaw rank shifted))) :
    Nonempty (Derivation body Delta (graph1 variableRankRaw rank raw)) := by
  apply programCases variableRankRaw (Fin.cons raw Fin.elim0) _
  intro beta j Theta before hj hb
  rw [graph1Rename]
  simp only [consTermRename,emptyRename] at hb
  have hs' := renameInto hs j Theta hj
  have hr' := renameInto hr j Theta hj
  rw [graph2Rename] at hs'
  rw [graph1Rename] at hr'
  have he := rankShiftEqual (raw.relabel j) (shifted.relabel j) before (rank.relabel j) (k.relabel j) hs' hb hr'
  simp only [equalEqn] at he
  obtain ⟨he⟩ := he
  exact outputTransport variableRankRaw before (rank.relabel j) (Fin.cons (raw.relabel j) Fin.elim0)
    ⟨InternalTagArithmeticSupportProof.symm he⟩ hb

theorem rankShiftBackward (raw shifted rank k : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph2 shiftRaw shifted k raw)))
    (hr : Nonempty (Derivation body Delta (graph1 variableRankRaw rank raw))) :
    Nonempty (Derivation body Delta (graph1 variableRankRaw rank shifted)) := by
  apply programCases variableRankRaw (Fin.cons shifted Fin.elim0) _
  intro beta j Theta after hj ha
  rw [graph1Rename]
  simp only [consTermRename,emptyRename] at ha
  have hs' := renameInto hs j Theta hj
  have hr' := renameInto hr j Theta hj
  rw [graph2Rename] at hs'
  rw [graph1Rename] at hr'
  have he := rankShiftEqual (raw.relabel j) (shifted.relabel j) (rank.relabel j) after (k.relabel j) hs' hr' ha
  simp only [equalEqn] at he
  exact outputTransport variableRankRaw after (rank.relabel j) (Fin.cons (shifted.relabel j) Fin.elim0) he ha

theorem rankEraseNonincrease (raw erased before after d k : OTerm alpha)
    (he : Nonempty (Derivation body Delta (graph3 eraseRaw erased d k raw)))
    (hb : Nonempty (Derivation body Delta (graph1 variableRankRaw before raw)))
    (ha : Nonempty (Derivation body Delta (graph1 variableRankRaw after erased))) :
    Nonempty (Derivation body Delta (RankNonincrease after before)) :=
  relationNonincrease after before
    (atRawApply (fold .erase) true raw d k erased before after (allRawTransport true raw) he hb ha)

theorem actualRawVariableRankShift : OriginalRawVariableRankTargets.ActualRawVariableRankShift := by
  intro positive alpha Delta raw shifted rank k
  let C := graph2 shiftRaw shifted k raw
  let G := graph1 variableRankRaw rank shifted
  let R := graph1 variableRankRaw rank raw
  have hcG : Nonempty (Derivation positive (G :: C :: Delta) C) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  have hcR : Nonempty (Derivation positive (R :: C :: Delta) C) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  obtain ⟨hf⟩ := rankShiftForward raw shifted rank k hcG ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := rankShiftBackward raw shifted rank k hcR ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩

theorem actualRawVariableRankErase : OriginalRawVariableRankTargets.ActualRawVariableRankErase := by
  intro positive alpha Delta raw erased before after d k
  let A := graph3 eraseRaw erased d k raw ⊓
    (graph1 variableRankRaw before raw ⊓ graph1 variableRankRaw after erased)
  have h : Nonempty (Derivation positive (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := rankEraseNonincrease raw erased before after d k (andLeft h) (andLeft (andRight h)) (andRight (andRight h))
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankTransportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankTransportProof
