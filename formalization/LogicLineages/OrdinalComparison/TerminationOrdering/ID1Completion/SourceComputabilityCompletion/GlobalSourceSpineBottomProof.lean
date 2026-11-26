module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.GlobalSourceSpineBottomSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.GlobalSourceSpineComputableProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.GlobalSourceSpineBottomProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open Source (Ty)
open InternalOriginalUniformDescentSelection (Data)
open InternalComputabilityApplication InternalComputabilityApplicationSyntaxProof
open InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsSyntaxProof (graph2Rename)
open InternalAcceptanceSupportProof (programCases)
open InternalControlGraphSupportProof (emptyRename)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalTagArithmeticSyntaxProof (OTerm)
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedSourceSyntaxProof (numeralRename)
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Construct the runtime pair internally. The final original target has
   only the actual original bottom Object graph as its internal premise. -/
theorem actualConcreteBottomComputable : ComputabilityLeastTargets.ActualConcreteBottomComputable := by
  intro n arity base hbase window hwindow oldSrc oldComp oldStep oldVertex oldResult
  dsimp only
  intro symbols S table hS
  let context := OrdinaryArithmeticQuotient.contextCode symbols S table
  let src := OuterSelection.source oldSrc oldComp base oldStep window
  let comp := OuterSelection.computability oldComp base window oldVertex oldResult
  intro tau htau α Delta object gamma
  let H := ComputabilityLeast.bottomGraph object
    (numeral (NumberedLeastCodeRepresentative.typeNumber tau)) gamma
  have hb : Nonempty (Derivation (SourcePresentation.sourceBody src context) (H :: Delta) H) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have result : Nonempty (Derivation (SourcePresentation.sourceBody src context) (H :: Delta)
      (computable comp tau (numeral context) object)) := by
    apply programCases InternalPairing.pairing
      (Fin.cons (numeral context) (Fin.cons gamma Fin.elim0)) _
    intro β j Theta parameter hj hp
    simp only [computableRename, numeralRename]
    have hp' : Nonempty (Derivation (SourcePresentation.sourceBody src context) Theta
        (graph2 InternalPairing.pairing parameter (numeral context) (gamma.relabel j))) := by
      simpa only [consTermRename, emptyRename, numeralRename] using hp
    have hb' := renameInto hb j Theta hj
    change Nonempty (Derivation (SourcePresentation.sourceBody src context) Theta
      ((ComputabilityLeast.bottomGraph object
        (numeral (NumberedLeastCodeRepresentative.typeNumber tau)) gamma).relabel j)) at hb'
    simp only [ComputabilityLeast.bottomGraph, graph2Rename, numeralRename] at hb'
    have ht := GlobalSourceSpineBottomSupportProof.runtimeBottomTyped n arity base hbase
      window hwindow oldComp oldVertex oldResult symbols S table hS tau htau
      (object.relabel j) (gamma.relabel j) parameter hp' hb'
    have hm := GlobalSourceSpineBottomSupportProof.bottomObjectMarked tau
      (object.relabel j) (gamma.relabel j) hb'
    exact GlobalSourceSpineComputableProof.computableSpine n arity base hbase window hwindow
      oldSrc oldComp oldStep oldVertex oldResult symbols S table hS tau β Theta
      (object.relabel j) (numeral (Nat.pair 1 0)) (numeral 0) ht hm
  obtain ⟨result⟩ := result
  exact ⟨Derivation.implicationIntroduction result⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.GlobalSourceSpineBottomProof
