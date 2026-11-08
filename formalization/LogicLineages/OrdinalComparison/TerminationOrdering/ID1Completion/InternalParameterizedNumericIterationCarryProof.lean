module
public import LogicLineages.Audit
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedNumericIterationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedNumericIterationCarryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open InternalParameterizedNumericIteration InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open InternalApplicationCertificateConstructorsSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem carryRename {α β : Type} (P : Program 2) (out state : OTerm α) (j : α → β) :
    (carryGraph P out state).relabel j = carryGraph P (out.relabel j) (state.relabel j) := by
  simp only [carryGraph,programRename,consTermRename,emptyRename]

theorem carryValue (P : Program 2) (state nextState value next parameter : OTerm α)
    (hs : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing state parameter value)))
    (ht : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing nextState parameter next)))
    (hp : Nonempty (Derivation body Gamma (programGraph P next (Fin.cons value (Fin.cons parameter Fin.elim0))))) :
    Nonempty (Derivation body Gamma (carryGraph P nextState state)) := by
  exact binaryValue InternalPairing.pairing InternalUnpair.left
    (.composition P ![InternalUnpair.right,InternalUnpair.left]) nextState parameter next
    (Fin.cons state Fin.elim0) ht (pairLeft state parameter value hs)
    (binaryValue P InternalUnpair.right InternalUnpair.left next value parameter
      (Fin.cons state Fin.elim0) hp (pairRight state parameter value hs) (pairLeft state parameter value hs))

theorem carryRecover (P : Program 2) (state nextState value next parameter : OTerm α)
    (hs : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing state parameter value)))
    (ht : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing nextState parameter next)))
    (hc : Nonempty (Derivation body Gamma (carryGraph P nextState state))) :
    Nonempty (Derivation body Gamma (programGraph P next (Fin.cons value (Fin.cons parameter Fin.elim0)))) := by
  apply programCases P (Fin.cons value (Fin.cons parameter Fin.elim0)) _
  intro β j Delta result hj hr
  simp only [programRename,consTermRename,emptyRename]
  simp only [consTermRename,emptyRename] at hr
  have hs' := renameInto hs j Delta hj
  rw [graph2Rename] at hs'
  have ht' := renameInto ht j Delta hj
  rw [graph2Rename] at ht'
  have hc' := renameInto hc j Delta hj
  rw [carryRename] at hc'
  have hv := binaryValue P InternalUnpair.right InternalUnpair.left result
    (value.relabel j) (parameter.relabel j) (Fin.cons (state.relabel j) Fin.elim0) hr
    (pairRight _ _ _ hs') (pairLeft _ _ _ hs')
  have hp := binaryRecover InternalPairing.pairing InternalUnpair.left
    (.composition P ![InternalUnpair.right,InternalUnpair.left]) (nextState.relabel j)
    (parameter.relabel j) result (Fin.cons (state.relabel j) Fin.elim0) hc'
    (pairLeft _ _ _ hs') hv
  have he := valueUnique InternalUnpair.right result (next.relabel j)
    (Fin.cons (nextState.relabel j) Fin.elim0) (pairRight _ _ _ hp) (pairRight _ _ _ ht')
  exact outputTransport P result (next.relabel j)
    (Fin.cons (value.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)) he hr

theorem carryPreserve (P : Program 2) (out state parameter : OTerm α)
    (hl : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left parameter state)))
    (hc : Nonempty (Derivation body Gamma (carryGraph P out state))) :
    Nonempty (Derivation body Gamma (graph1 InternalUnpair.left parameter out)) := by
  apply programCases (.composition P ![InternalUnpair.right,InternalUnpair.left])
    (Fin.cons state Fin.elim0) _
  intro β j Delta result hj hr
  rw [graph1Rename]
  simp only [consTermRename,emptyRename] at hr
  have hl' := renameInto hl j Delta hj
  rw [graph1Rename] at hl'
  have hc' := renameInto hc j Delta hj
  rw [carryRename] at hc'
  exact pairLeft (out.relabel j) (parameter.relabel j) result
    (binaryRecover InternalPairing.pairing InternalUnpair.left
      (.composition P ![InternalUnpair.right,InternalUnpair.left]) (out.relabel j)
      (parameter.relabel j) result (Fin.cons (state.relabel j) Fin.elim0) hc' hl' hr)

theorem actualOriginalParameterizedNumericIterationCarryStep :
    InternalParameterizedNumericIterationTargets.ActualOriginalParameterizedNumericIterationCarryStep := by
  intro body P α Gamma state nextState value next parameter
  let A := graph2 InternalPairing.pairing state parameter value ⊓
    graph2 InternalPairing.pairing nextState parameter next
  let C := carryGraph P nextState state
  let Q := programGraph P next (Fin.cons value (Fin.cons parameter Fin.elim0))
  have forward : Nonempty (Derivation body (C :: A :: Gamma) Q) := by
    have ha : Derivation body (C :: A :: Gamma) A :=
      Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
    exact carryRecover P state nextState value next parameter
      ⟨Derivation.conjunctionLeft ha⟩ ⟨Derivation.conjunctionRight ha⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩
  have backward : Nonempty (Derivation body (Q :: A :: Gamma) C) := by
    have ha : Derivation body (Q :: A :: Gamma) A :=
      Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
    exact carryValue P state nextState value next parameter
      ⟨Derivation.conjunctionLeft ha⟩ ⟨Derivation.conjunctionRight ha⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨forward⟩ := forward
  obtain ⟨backward⟩ := backward
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction forward) (Derivation.implicationIntroduction backward))⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedNumericIterationCarryProof

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedNumericIterationCarryProof
