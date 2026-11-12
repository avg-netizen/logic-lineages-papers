module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawObjectRankTransportSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawObjectRankTransportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionTotalityProof
open InternalRecursionClosureProof
open OriginalRawObjectTransport OriginalRawObjectTransportInternalExposureProof
open OriginalRawObjectTransportInternalSyntaxProof OriginalRawObjectRankTransportSupportProof
open OriginalLambdaConstructorGraphSyntaxProof (andLeft andRight)
open OriginalRawSyntaxTransport OriginalRawVariableRank
open OriginalRawVariableRankPackedTransportProof OriginalRawVariableRankPackedQueryProof
open SourceComputabilityFormulaSupportProof (numeral)

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Every pair coordinate is supplied by the original internal shift exposure. -/
theorem rankShiftObjectForward (d input shifted rank : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph2 shiftObjectRaw shifted d input)))
    (hr : Nonempty (Derivation body Delta (graph1 variableRankObjectRaw rank shifted))) :
    Nonempty (Derivation body Delta (graph1 variableRankObjectRaw rank input)) := by
  apply actualRawObjectInternalShiftExposure body alpha Delta d input shifted _ hs
  intro beta j Theta hj gamma packed extendedGamma shiftedPacked hf
  rw [graph1Rename]
  have hp := andLeft hf
  have ht := andLeft (andRight (andRight hf))
  have ho := andRight (andRight (andRight hf))
  have hr' := unaryRename variableRankObjectRaw rank shifted hr j Theta hj
  exact rankObjectBackward (input.relabel j) (rank.relabel j) gamma packed hp
    (rankShiftPackedForward packed shiftedPacked (rank.relabel j) (numeral 0) ht
      (rankObjectForward (shifted.relabel j) (rank.relabel j) extendedGamma shiftedPacked ho hr'))

/-- The reverse graph implication uses the same recovered shift payload. -/
theorem rankShiftObjectBackward (d input shifted rank : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph2 shiftObjectRaw shifted d input)))
    (hr : Nonempty (Derivation body Delta (graph1 variableRankObjectRaw rank input))) :
    Nonempty (Derivation body Delta (graph1 variableRankObjectRaw rank shifted)) := by
  apply actualRawObjectInternalShiftExposure body alpha Delta d input shifted _ hs
  intro beta j Theta hj gamma packed extendedGamma shiftedPacked hf
  rw [graph1Rename]
  have hp := andLeft hf
  have ht := andLeft (andRight (andRight hf))
  have ho := andRight (andRight (andRight hf))
  have hr' := unaryRename variableRankObjectRaw rank input hr j Theta hj
  exact rankObjectBackward (shifted.relabel j) (rank.relabel j) extendedGamma shiftedPacked ho
    (rankShiftPackedBackward packed shiftedPacked (rank.relabel j) (numeral 0) ht
      (rankObjectForward (input.relabel j) (rank.relabel j) gamma packed hp hr'))

/-- Totality supplies the original head, tail and payload outputs even when
the raw context does not encode a cons. Only the numeric rank is transported. -/
theorem rankEraseObjectNonincrease (input erased before after : OTerm alpha)
    (he : Nonempty (Derivation body Delta (graph1 eraseObjectRaw erased input)))
    (hb : Nonempty (Derivation body Delta (graph1 variableRankObjectRaw before input)))
    (ha : Nonempty (Derivation body Delta (graph1 variableRankObjectRaw after erased))) :
    Nonempty (Derivation body Delta (RankNonincrease after before)) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons input Fin.elim0
  apply supplyOutputs body 1 5 (fun i => OrdinaryArithmetic.graphFormula (eraseRankQueries i))
    (fun i => (actualOriginalPrograms body 1 (eraseRankQueries i)).1)
    alpha Delta xs (RankNonincrease after before)
  intro beta j Theta ys hj hq
  rw [rankNonincreaseRename]
  have hq' : ∀ i, Nonempty (Derivation body Theta
      (programGraph (eraseRankQueries i) (ys i) (Fin.cons (input.relabel j) Fin.elim0))) :=
    fun i => queryOneRename (eraseRankQueries i) input j Theta (ys i) (hq i)
  exact rankEraseObjectAt (input.relabel j) (erased.relabel j)
    (before.relabel j) (after.relabel j) ys hq'
    (unaryRename eraseObjectRaw erased input he j Theta hj)
    (unaryRename variableRankObjectRaw before input hb j Theta hj)
    (unaryRename variableRankObjectRaw after erased ha j Theta hj)

theorem actualOriginalRawObjectShiftRank :
    OriginalRawObjectRankTransportTargets.ActualOriginalRawObjectShiftRank := by
  intro positive alpha Delta d input shifted rank
  let C := graph2 shiftObjectRaw shifted d input
  let G := graph1 variableRankObjectRaw rank shifted
  let R := graph1 variableRankObjectRaw rank input
  have hcG : Nonempty (Derivation positive (G :: C :: Delta) C) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  have hcR : Nonempty (Derivation positive (R :: C :: Delta) C) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  obtain ⟨hf⟩ := rankShiftObjectForward d input shifted rank hcG
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := rankShiftObjectBackward d input shifted rank hcR
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩

theorem actualOriginalRawObjectEraseRank :
    OriginalRawObjectRankTransportTargets.ActualOriginalRawObjectEraseRank := by
  intro positive alpha Delta input erased before after
  let A := graph1 eraseObjectRaw erased input ⊓
    (graph1 variableRankObjectRaw before input ⊓ graph1 variableRankObjectRaw after erased)
  have h : Nonempty (Derivation positive (A :: Delta) A) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := rankEraseObjectNonincrease input erased before after
    (andLeft h) (andLeft (andRight h)) (andRight (andRight h))
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawObjectRankTransportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawObjectRankTransportProof
