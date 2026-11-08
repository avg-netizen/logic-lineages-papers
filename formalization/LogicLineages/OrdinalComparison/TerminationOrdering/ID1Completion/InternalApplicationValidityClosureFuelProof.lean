module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendRunProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPairingSumBoundsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityClosureFuelProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationValidityStackAppend InternalPairingSumBounds
open InternalApplicationValidityStackAppendRunProof InternalApplicationValidityStackAppendSyntaxProof
open InternalUnpairReverseSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalOriginalOrderSyntaxProof InternalApplicationCertificateConstructorsSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- The padding witness is obtained internally from weak order. Success is
then preserved by the actual numeric iterator, not a semantic model argument. -/
theorem successAtBound (node leaf : Program 1) (count fuel work : OTerm α)
    (hb : Nonempty (Derivation body Gamma (weakBound count fuel)))
    (hs : Nonempty (Derivation body Gamma (successfulWork node leaf count work))) :
    Nonempty (Derivation body Gamma (successfulWork node leaf fuel work)) := by
  apply weakOrderCases Gamma count fuel _ hb
  intro β j Delta padding hj he
  rw [successfulWorkRename]
  have hs' := renameInto hs j Delta hj
  rw [successfulWorkRename] at hs'
  exact countTransport node leaf (OrdinaryArithmetic.addTerm (count.relabel j) padding)
    (fuel.relabel j) (work.relabel j) he
    (successPadding node leaf (count.relabel j) padding (work.relabel j) hs')

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityClosureFuelProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityClosureFuelProof
