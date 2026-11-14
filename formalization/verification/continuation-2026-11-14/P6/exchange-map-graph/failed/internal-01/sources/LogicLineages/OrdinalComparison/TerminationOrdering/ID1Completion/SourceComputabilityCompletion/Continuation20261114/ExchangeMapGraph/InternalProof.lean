module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeMapGraph.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMembership.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeMapGraph.InternalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalAcceptanceBranchProof InternalAcceptanceConjunctionProof
open InternalGraphCompositionFunctionalityProof InternalTagArithmeticSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn eqnRelabel zRelabel sucRelabel)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem entryFields (entry k value rest key : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing entry k value))) :
    Nonempty (Derivation body Delta
      (programGraph entryKey k ![entry,rest,key] ⊓ programGraph entryValue value ![entry,rest,key])) := by
  obtain ⟨hi⟩ := InternalPositiveUnfoldingSupportProof.closedApply
    (InternalUnpairProof.actualOriginalGeneratedCodeInverse body alpha entry k value) hp
  obtain ⟨hl⟩ := unaryValue InternalUnpair.left (.projection 0) k entry ![entry,rest,key]
    ⟨Derivation.conjunctionLeft hi⟩ (projectionValue 0 ![entry,rest,key])
  obtain ⟨hr⟩ := unaryValue InternalUnpair.right (.projection 0) value entry ![entry,rest,key]
    ⟨Derivation.conjunctionRight hi⟩ (projectionValue 0 ![entry,rest,key])
  exact ⟨Derivation.conjunctionIntroduction hl hr⟩

theorem hitStep (entry key value rest : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing entry key value))) :
    Nonempty (Derivation body Delta (programGraph lookupStep (suc value) ![entry,rest,key])) := by
  obtain ⟨hf⟩ := entryFields entry key value rest key hp
  let xs : Fin 3 → OTerm alpha := ![entry,rest,key]
  have he := binaryValue InternalEqualityTest.equalityTest entryKey (.projection 2) (suc z) key key xs
    (InternalEqualityTestCompositionProof.equalitySelf key) ⟨Derivation.conjunctionLeft hf⟩ (projectionValue 2 xs)
  have hv := unaryValue .succ entryValue (suc value) value xs
    (successorValue (Fin.cons value Fin.elim0)) ⟨Derivation.conjunctionRight hf⟩
  exact successorBranchIntro _ _ _ (suc value) z xs he hv

theorem missStep (entry k value rest key : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing entry k value)))
    (hn : Nonempty (Derivation body Delta (eqn k key).not)) :
    Nonempty (Derivation body Delta (programGraph lookupStep rest ![entry,rest,key])) := by
  obtain ⟨hf⟩ := entryFields entry k value rest key hp
  let xs : Fin 3 → OTerm alpha := ![entry,rest,key]
  have hn' : Nonempty (Derivation body Delta (equal k key).not) := by simpa only [equalEqn] using hn
  have he := OriginalRawSyntaxTransportInternalConstructorSupportProof.sameReject entryKey (.projection 2) k key xs
    ⟨Derivation.conjunctionLeft hf⟩ (projectionValue 2 xs) hn'
  exact zeroBranchIntro _ _ _ rest xs he (projectionValue 1 xs)

theorem internalFirstHit : Targets.InternalFirstHit := by
  intro body alpha Delta code entry tail key value hc hp
  apply programCases lookup (Fin.cons tail (Fin.cons key Fin.elim0)) _
  intro beta j Theta rest hj hr
  simp only [graph2Rename,sucRelabel]
  simp only [consTermRename,emptyRename] at hr
  have hc' := renameInto hc j Theta hj
  rw [graph2Rename] at hc'
  have hp' := renameInto hp j Theta hj
  rw [graph2Rename] at hp'
  exact InternalRawListRecursionProof.consValue (InternalAcceptance.constantZero 1) lookupStep
    (code.relabel j) (entry.relabel j) (tail.relabel j) rest (suc (value.relabel j))
    (Fin.cons (key.relabel j) Fin.elim0) hc' hr
    (hitStep (entry.relabel j) (key.relabel j) (value.relabel j) rest hp')

theorem missForward (code entry tail k value key out : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code entry tail)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing entry k value)))
    (hn : Nonempty (Derivation body Delta (eqn k key).not))
    (hr : Nonempty (Derivation body Delta (graph2 lookup out tail key))) :
    Nonempty (Derivation body Delta (graph2 lookup out code key)) :=
  InternalRawListRecursionProof.consValue (InternalAcceptance.constantZero 1) lookupStep
    code entry tail out out (Fin.cons key Fin.elim0) hc hr (missStep entry k value out key hp hn)

theorem internalMissTail : Targets.InternalMissTail := by
  intro body alpha Delta code entry tail k value key out hc hp hn
  constructor
  · intro h
    apply programCases lookup (Fin.cons tail (Fin.cons key Fin.elim0)) _
    intro beta j Theta rest hj hr
    rw [graph2Rename]
    simp only [consTermRename,emptyRename] at hr
    have hc' := renameInto hc j Theta hj
    rw [graph2Rename] at hc'
    have hp' := renameInto hp j Theta hj
    rw [graph2Rename] at hp'
    have hn' := renameInto hn j Theta hj
    change Nonempty (Derivation body Theta ((eqn k key).relabel j).not) at hn'
    rw [eqnRelabel] at hn'
    have h' := renameInto h j Theta hj
    rw [graph2Rename] at h'
    have hm := missForward (code.relabel j) (entry.relabel j) (tail.relabel j) (k.relabel j)
      (value.relabel j) (key.relabel j) rest hc' hp' hn' hr
    have hu := valueUnique lookup rest (out.relabel j) ![code.relabel j,key.relabel j] hm h'
    exact outputTransport lookup rest (out.relabel j) ![tail.relabel j,key.relabel j] hu hr
  · exact missForward code entry tail k value key out hc hp hn

theorem mapMissingStep (key rest entries : OTerm alpha)
    (hz : Nonempty (Derivation body Delta (graph2 lookup z entries key))) :
    Nonempty (Derivation body Delta (programGraph mapStep rest ![key,rest,entries])) := by
  let xs : Fin 3 → OTerm alpha := ![key,rest,entries]
  have hf := binaryValue lookup (.projection 2) (.projection 0) z entries key xs hz
    (projectionValue 2 xs) (projectionValue 0 xs)
  exact zeroBranchIntro found (.projection 1) _ rest xs hf (projectionValue 1 xs)

theorem mapMissingForward (keys key tail entries out : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode keys key tail)))
    (hz : Nonempty (Derivation body Delta (graph2 lookup z entries key)))
    (hr : Nonempty (Derivation body Delta (graph2 mapGraph out tail entries))) :
    Nonempty (Derivation body Delta (graph2 mapGraph out keys entries)) :=
  InternalRawListRecursionProof.consValue (InternalAcceptance.constantZero 1) mapStep
    keys key tail out out (Fin.cons entries Fin.elim0) hc hr (mapMissingStep key out entries hz)

theorem internalMapMissing : Targets.InternalMapMissing := by
  intro body alpha Delta keys key tail entries out hc hz
  constructor
  · intro h
    apply programCases mapGraph (Fin.cons tail (Fin.cons entries Fin.elim0)) _
    intro beta j Theta rest hj hr
    rw [graph2Rename]
    simp only [consTermRename,emptyRename] at hr
    have hc' := renameInto hc j Theta hj
    rw [graph2Rename] at hc'
    have hz' := renameInto hz j Theta hj
    simp only [graph2Rename,zRelabel] at hz'
    have h' := renameInto h j Theta hj
    rw [graph2Rename] at h'
    have hm := mapMissingForward (keys.relabel j) (key.relabel j) (tail.relabel j)
      (entries.relabel j) rest hc' hz' hr
    have hu := valueUnique mapGraph rest (out.relabel j) ![keys.relabel j,entries.relabel j] hm h'
    exact outputTransport mapGraph rest (out.relabel j) ![tail.relabel j,entries.relabel j] hu hr
  · exact mapMissingForward keys key tail entries out hc hz
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeMapGraph.InternalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeMapGraph.InternalProof
