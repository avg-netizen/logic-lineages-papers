module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeSymmetry.QueriesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedHeadRecurrences.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalHeadMoveReversal.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.DescentProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeSymmetry.NumberedAtChildrenProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115 Continuation20261116
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open Definitions FieldsSyntaxProof AllSyntaxProof SyntaxProof BindingProof FactsProof
open InternalTagArithmeticSyntaxProof (sucRelabel zRelabel eqnRelabel)
open InternalTagArithmeticSupportProof (symm)
open InternalApplicationValidityStackAppendFrameQueryProof (weakenProof)
open OriginalRawSyntaxTransportInternalConstructorArityCasesProof (orCases)
open InternalQuotientComparisonProof (orLeft orRight)
theorem atChildren (n : Nat) (arity : Fin n → Nat)
    (left right k l f g tau upsilon base dest ts us extras others node rev window symbols types first rfirst last rlast : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor left ![k,f,tau,base,ts,extras])))
    (hrc : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor right ![l,g,upsilon,dest,us,others])))
    (h : Facts (body := body) (Delta := Delta) n arity left right node rev window symbols types)
    (ih : Nonempty (Derivation body Delta (BelowRaw n arity left)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing first base dest)))
    (hrp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rfirst dest base)))
    (hq : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing last extras others)))
    (hrq : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rlast others extras))) :
    Nonempty (Derivation body Delta (graph2 (OriginalDecodedExchangeEquation.exchange n arity) (suc z) rev window)) := by
  have hf := (OriginalDecodedHeadRecurrences.Proof.numbered n arity body alpha Delta
    left right k l f g tau upsilon base dest ts us extras others node first last window symbols types
    hlc hrc h.pair hp hq h.windowPair).mp h.exchange
  have heads := OriginalGuardedHeadEquality.Proof.guardHeads n true body alpha Delta
    left right k l f g tau upsilon base dest ts us extras others node z window hlc hrc h.pair (andLeft hf)
  have small := OriginalTypedEnumerationDepthBound.DescentProof.numbered left k f tau base ts extras hlc
  apply (OriginalDecodedHeadRecurrences.Proof.numbered n arity body alpha Delta
    right left l k g f upsilon tau dest base us ts others extras rev rfirst rlast window symbols types
    hrc hlc h.reversePair hrp hrq h.windowPair).mpr
  apply andIntro (reverseGuard h)
  have hm := andLeft (andRight hf)
  obtain ⟨hk⟩ := andLeft hm
  obtain ⟨ht⟩ := andLeft (andRight hm)
  obtain ⟨hs⟩ := andRight (andRight hm)
  apply andIntro (andIntro ⟨symm hk⟩ (andIntro ⟨symm ht⟩ ⟨symm hs⟩))
  apply orCases (andRight (andRight hf))
  · intro Theta hi hb
    apply orCases hb
    · intro Xi hj hm
      have hh := OriginalHeadMoveReversal.Proof.reversal n arity body alpha Xi
        f base g dest symbols types (weakenProof (andLeft heads) (fun p hp => hj p (hi p hp)))
        (weakenProof h.closed (fun p hp => hj p (hi p hp))) (andRight hm)
      obtain ⟨heq⟩ := andLeft hm
      obtain ⟨ha⟩ := andIntro ⟨symm heq⟩ hh
      exact ⟨orLeft (orLeft ha)⟩
    · intro Xi hj hm
      let inc : ∀ p ∈ Delta, p ∈ Xi := fun p hp => hj p (hi p hp)
      have hh := childReverse left base dest first rfirst window symbols types
        (weakenProof ih inc) (weakenProof (andLeft small) inc) (weakenProof hp inc) (weakenProof hrp inc)
        (weakenProof h.windowPair inc) (weakenProof h.closed inc) (andRight hm)
      obtain ⟨heq⟩ := andLeft (andLeft hm)
      obtain ⟨hext⟩ := andRight (andLeft hm)
      obtain ⟨ha⟩ := andIntro (andIntro ⟨symm heq⟩ ⟨symm hext⟩) hh
      exact ⟨orLeft (orRight ha)⟩
  · intro Theta hi hb
    have hh := childReverse left extras others last rlast window symbols types
      (weakenProof ih hi) (weakenProof (andRight small) hi) (weakenProof hq hi) (weakenProof hrq hi)
      (weakenProof h.windowPair hi) (weakenProof h.closed hi) (andRight hb)
    obtain ⟨heq⟩ := andLeft (andLeft hb)
    obtain ⟨hbase⟩ := andRight (andLeft hb)
    obtain ⟨ha⟩ := andIntro (andIntro ⟨symm heq⟩ ⟨symm hbase⟩) hh
    exact ⟨orRight ha⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeSymmetry.NumberedAtChildrenProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeSymmetry.NumberedAtChildrenProof
