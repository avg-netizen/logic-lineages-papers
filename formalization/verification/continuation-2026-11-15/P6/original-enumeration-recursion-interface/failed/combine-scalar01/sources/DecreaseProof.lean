module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursionInterface.DependencyPositiveProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursionInterface.DecreaseProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof (refl)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)

theorem internalDecrease : Targets.InternalDecrease := by
  intro body alpha Delta node param deps child parentRank childRank hd hm hr hcr
  apply zeroSuccessorCases Delta parentRank _
  · let A := eqn parentRank z
    have he : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hz := outputTransport R parentRank z ![node,param] he (withHyp hr A)
    obtain ⟨hf⟩ := DependencySupportProof.zeroImpossible node param deps child hz (withHyp hd A) (withHyp hm A)
    exact ⟨Derivation.explosion hf⟩
  · intro beta j Theta f hj he
    simp only [InternalLessThan.strictLess,InternalOriginalOrderSyntaxProof.orderRename]
    have hrj := InternalGraphCompositionFunctionalityProof.renameInto hr j Theta hj
    have hdj := InternalGraphCompositionFunctionalityProof.renameInto hd j Theta hj
    have hmj := InternalGraphCompositionFunctionalityProof.renameInto hm j Theta hj
    have hcrj := InternalGraphCompositionFunctionalityProof.renameInto hcr j Theta hj
    simp only [graph2Rename,OriginalRawSyntaxTransportInternalConstructorSelectorBoundsProof.numeralRelabel] at hrj hdj hmj hcrj
    have hs := outputTransport R (parentRank.relabel j) (suc f) ![node.relabel j,param.relabel j] he hrj
    have hp := DependencyPositiveProof.positive (node.relabel j) (param.relabel j) (deps.relabel j)
      (child.relabel j) (childRank.relabel j) f hs hdj hmj hcrj
    exact InternalOriginalPairingOrderArithmeticProof.strictTransport
      (childRank.relabel j) (parentRank.relabel j) (childRank.relabel j) (suc f)
      ⟨refl (childRank.relabel j)⟩ he hp
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursionInterface.DecreaseProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursionInterface.DecreaseProof
