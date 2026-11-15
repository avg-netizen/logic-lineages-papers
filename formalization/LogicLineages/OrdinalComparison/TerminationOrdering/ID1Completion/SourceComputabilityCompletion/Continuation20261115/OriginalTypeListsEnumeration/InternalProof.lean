module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsEnumeration.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsEnumeration.InternalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalTagArithmeticSupportProof
open InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open InternalRecursionGraphStepSyntaxProof
open OriginalRawSyntaxTransportInternalVariableSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem stepValue (count previous types rows out : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 cross rows types previous)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode out z rows))) :
    Nonempty (Derivation body Delta (graph3 step out count previous types)) := by
  apply binaryValue InternalListCodec.consCode (OriginalRawSyntaxTransport.constant 3 0)
    (.composition cross ![.projection 2,.projection 1]) out z rows
    ![count,previous,types] hc (constantValue 0 ![count,previous,types])
  exact binaryValue cross (.projection 2) (.projection 1) rows types previous
    ![count,previous,types] hr (projectionValue 2 ![count,previous,types])
    (projectionValue 1 ![count,previous,types])

theorem successorValue (count types previous rows out : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 enumeration previous count types)))
    (hr : Nonempty (Derivation body Delta (graph2 cross rows types previous)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode out z rows))) :
    Nonempty (Derivation body Delta (graph2 enumeration out (suc count) types)) := by
  have hs := stepValue count previous types rows out hr hc
  unfold graph2 enumeration programGraph at hp ⊢
  unfold graph3 programGraph at hs
  change Nonempty (Derivation body Delta (InternalRecursionGraph.recursion
    (OrdinaryArithmetic.graphFormula (InternalLessThan.constantOne 1))
    (OrdinaryArithmetic.graphFormula step) previous count (Fin.cons types Fin.elim0))) at hp
  change Nonempty (Derivation body Delta (InternalRecursionGraph.recursion
    (OrdinaryArithmetic.graphFormula (InternalLessThan.constantOne 1))
    (OrdinaryArithmetic.graphFormula step) out (suc count) (Fin.cons types Fin.elim0)))
  exact InternalRecursionGraphSuccessorIntroductionProof.recursionSuccessorIntroduction Delta
    (OrdinaryArithmetic.graphFormula (InternalLessThan.constantOne 1))
    (OrdinaryArithmetic.graphFormula step) out count previous (Fin.cons types Fin.elim0) hp hs

theorem internalZero : Targets.InternalZero := by
  intro body alpha Delta types
  exact recursionZeroValue (InternalLessThan.constantOne 1) step (numeral 1)
    (Fin.cons types Fin.elim0) (InternalLessThanSupportProof.oneConstantValue (Fin.cons types Fin.elim0))

theorem internalSuccessor : Targets.InternalSuccessor := by
  intro body alpha Delta count types previous rows out hp hr
  constructor
  · intro ho
    apply programCases InternalListCodec.consCode (Fin.cons z (Fin.cons rows Fin.elim0)) _
    intro beta j Theta value hj hv
    rw [graph2Rename,zRelabel]
    simp only [consTermRename,emptyRename,zRelabel] at hv
    have hpj := InternalGraphCompositionFunctionalityProof.renameInto hp j Theta hj
    rw [graph2Rename] at hpj
    have hrj := InternalGraphCompositionFunctionalityProof.renameInto hr j Theta hj
    rw [graph2Rename] at hrj
    have hoj := InternalGraphCompositionFunctionalityProof.renameInto ho j Theta hj
    rw [graph2Rename,sucRelabel] at hoj
    have hval := successorValue (count.relabel j) (types.relabel j) (previous.relabel j)
      (rows.relabel j) value hpj hrj hv
    obtain ⟨he⟩ := valueUnique enumeration (out.relabel j) value
      (Fin.cons (suc (count.relabel j)) (Fin.cons (types.relabel j) Fin.elim0)) hoj hval
    exact outputTransport InternalListCodec.consCode value (out.relabel j)
      (Fin.cons z (Fin.cons (rows.relabel j) Fin.elim0)) ⟨symm he⟩ hv
  · intro hc
    exact successorValue count types previous rows out hp hr hc
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsEnumeration.InternalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsEnumeration.InternalProof
