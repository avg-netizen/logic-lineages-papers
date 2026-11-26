module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.CountQueriesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.CountEffectIntroProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.CountKeepProof
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

theorem atQuery (left right head tail rest needle query lc rc bit : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode left head tail)))
    (hrc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode right head rest)))
    (h : Nonempty (Derivation body Delta (countEffect tail needle rest bit)))
    (hl : Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count lc left query)))
    (hr : Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count rc right query))) :
    Nonempty (Derivation body Delta
      (((eqn needle query).imp (eqn lc (OrdinaryArithmetic.addTerm rc bit))) ⊓
       ((eqn needle query).not.imp (eqn lc rc)))) := by
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases CountQueriesProof.queries ![tail,rest,query] _
  intro beta j ys Theta hj hq
  have hx : (fun i => (![tail,rest,query] i).relabel j) = ![tail.relabel j,rest.relabel j,query.relabel j] := by
    funext i; fin_cases i <;> rfl
  rw [hx] at hq
  obtain ⟨ht,hs⟩ := CountQueriesProof.recover (tail.relabel j) (rest.relabel j) (query.relabel j) ys hq
  simp only [conjunctionRename,impRename,notRename,eqnRelabel,addRelabel]
  have hlcj := renameInto hlc j Theta hj
  have hrcj := renameInto hrc j Theta hj
  have hhj := renameInto h j Theta hj
  have hlj := renameInto hl j Theta hj
  have hrj := renameInto hr j Theta hj
  simp only [graph2Rename] at hlcj hrcj hlj hrj
  rw [countEffectRename] at hhj
  exact CountKeepAtProof.atCounts (left.relabel j) (right.relabel j) (head.relabel j) (tail.relabel j)
    (rest.relabel j) (needle.relabel j) (query.relabel j) (lc.relabel j) (rc.relabel j) (ys 0) (ys 1) (bit.relabel j)
    hlcj hrcj hhj hlj hrj ht hs

theorem keep (left right head tail rest needle bit : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode left head tail)))
    (hrc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode right head rest)))
    (h : Nonempty (Derivation body Delta (countEffect tail needle rest bit))) :
    Nonempty (Derivation body Delta (countEffect left needle right bit)) := by
  apply CountEffectIntroProof.introduce left needle right bit
  intro beta j Theta query lc rc hj hl hr
  have hlcj := renameInto hlc j Theta hj
  have hrcj := renameInto hrc j Theta hj
  have hhj := renameInto h j Theta hj
  rw [graph2Rename] at hlcj hrcj
  rw [countEffectRename] at hhj
  exact atQuery (left.relabel j) (right.relabel j) (head.relabel j) (tail.relabel j)
    (rest.relabel j) (needle.relabel j) query lc rc (bit.relabel j) hlcj hrcj hhj hl hr

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.CountKeepProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.CountKeepProof
