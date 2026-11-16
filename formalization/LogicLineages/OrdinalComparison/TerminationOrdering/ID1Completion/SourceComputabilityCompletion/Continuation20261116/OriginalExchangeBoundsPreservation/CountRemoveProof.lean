module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.CountRemoveAtProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.CountEffectIntroProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.CountRemoveProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof (programCases)
open InternalTagArithmeticSyntaxProof (z suc eqn eqnRelabel sucRelabel zRelabel)
open InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open InternalBetaExtensionSyntaxProof (impRename)
open OriginalTypedDecoderTransportLogicalProof (notRename)
open InternalOriginalOrderSyntaxProof (addRelabel)
open EraseInvariant EraseInvariantSyntaxProof Continuation20261114
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem atQuery (list head tail needle rest query lc rc : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode list head tail)))
    (he : Nonempty (Derivation body Delta (eqn head needle)))
    (h : Nonempty (Derivation body Delta (countEffect tail needle rest z)))
    (hl : Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count lc list query)))
    (hr : Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count rc rest query))) :
    Nonempty (Derivation body Delta
      (((eqn needle query).imp (eqn lc (OrdinaryArithmetic.addTerm rc (suc z)))) ⊓
       ((eqn needle query).not.imp (eqn lc rc)))) := by
  apply programCases ArgumentEntryCount.count ![tail,query] _
  intro beta j Theta tc hj ht
  have hx : (fun i => (![tail,query] i).relabel j) = ![tail.relabel j,query.relabel j] := by
    funext i; fin_cases i <;> rfl
  rw [hx] at ht
  simp only [conjunctionRename,impRename,notRename,eqnRelabel,addRelabel,sucRelabel,zRelabel]
  have hcj := renameInto hc j Theta hj
  have hej := renameInto he j Theta hj
  have hhj := renameInto h j Theta hj
  have hlj := renameInto hl j Theta hj
  have hrj := renameInto hr j Theta hj
  simp only [graph2Rename] at hcj hlj hrj
  rw [eqnRelabel] at hej
  simp only [countEffectRename,zRelabel] at hhj
  exact CountRemoveAtProof.atCounts (list.relabel j) (head.relabel j) (tail.relabel j)
    (needle.relabel j) (rest.relabel j) (query.relabel j) (lc.relabel j) tc (rc.relabel j)
    hcj hej hhj hlj ht hrj

theorem remove (list head tail needle rest : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode list head tail)))
    (he : Nonempty (Derivation body Delta (eqn head needle)))
    (h : Nonempty (Derivation body Delta (countEffect tail needle rest z))) :
    Nonempty (Derivation body Delta (countEffect list needle rest (suc z))) := by
  apply CountEffectIntroProof.introduce list needle rest (suc z)
  intro beta j Theta query lc rc hj hl hr
  simp only [sucRelabel,zRelabel]
  have hcj := renameInto hc j Theta hj
  have hej := renameInto he j Theta hj
  have hhj := renameInto h j Theta hj
  rw [graph2Rename] at hcj
  rw [eqnRelabel] at hej
  simp only [countEffectRename,zRelabel] at hhj
  exact atQuery (list.relabel j) (head.relabel j) (tail.relabel j) (needle.relabel j)
    (rest.relabel j) query lc rc hcj hej hhj hl hr

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.CountRemoveProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.CountRemoveProof
