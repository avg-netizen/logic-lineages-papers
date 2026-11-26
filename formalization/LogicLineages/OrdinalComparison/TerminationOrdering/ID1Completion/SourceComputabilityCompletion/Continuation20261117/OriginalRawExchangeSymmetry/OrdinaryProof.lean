module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeSymmetry.QueriesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeSymmetry.ResultSymmetryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedHeadRecurrences.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalHeadMoveReversal.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.DescentProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeSymmetry.OrdinaryProof
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
    (left right f g base dest node rev window symbols types child reversed : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.ordinaryConstructor left f base)))
    (hrc : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.ordinaryConstructor right g dest)))
    (h : Facts (body := body) (Delta := Delta) n arity left right node rev window symbols types)
    (ih : Nonempty (Derivation body Delta (BelowRaw n arity left)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing child base dest)))
    (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing reversed dest base))) :
    Nonempty (Derivation body Delta (graph2 (OriginalDecodedExchangeEquation.exchange n arity) (suc z) rev window)) := by
  have hf := (OriginalDecodedHeadRecurrences.Proof.ordinary n arity body alpha Delta
    left right f g base dest node child window symbols types hlc hrc h.pair hp h.windowPair).mp h.exchange
  have heads := OriginalGuardedHeadEquality.Proof.guardHeads n false body alpha Delta
    left right z z f g z z base dest z z z z node z window hlc hrc h.pair (andLeft hf)
  apply (OriginalDecodedHeadRecurrences.Proof.ordinary n arity body alpha Delta
    right left g f dest base rev reversed window symbols types hrc hlc h.reversePair hr h.windowPair).mpr
  apply andIntro (reverseGuard h)
  apply orCases (andRight hf)
  · intro Theta hi hb
    have hm := OriginalHeadMoveReversal.Proof.reversal n arity body alpha Theta
      f base g dest symbols types (weakenProof (andLeft heads) hi) (weakenProof h.closed hi) (andLeft hb)
    have hre := ResultSymmetryProof.symmetric g f (andRight hb)
    obtain ⟨ha⟩ := andIntro hm hre
    exact ⟨orLeft ha⟩
  · intro Theta hi hb
    obtain ⟨heq⟩ := andLeft hb
    have small := OriginalTypedEnumerationDepthBound.DescentProof.ordinary left f base (weakenProof hlc hi)
    have hh := childReverse left base dest child reversed window symbols types
      (weakenProof ih hi) small (weakenProof hp hi) (weakenProof hr hi)
      (weakenProof h.windowPair hi) (weakenProof h.closed hi) (andRight hb)
    obtain ⟨ha⟩ := andIntro ⟨symm heq⟩ hh
    exact ⟨orRight ha⟩

theorem reversed (n : Nat) (arity : Fin n → Nat)
    (left right f g base dest node rev window symbols types : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.ordinaryConstructor left f base)))
    (hrc : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.ordinaryConstructor right g dest)))
    (h : Facts (body := body) (Delta := Delta) n arity left right node rev window symbols types)
    (ih : Nonempty (Derivation body Delta (BelowRaw n arity left))) :
    Nonempty (Derivation body Delta (graph2 (OriginalDecodedExchangeEquation.exchange n arity) (suc z) rev window)) := by
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases QueriesProof.unary ![base,dest] _
  intro beta j ys Theta hj hq
  rw [QueriesProof.vector2Rename] at hq
  simp only [graph2Rename,sucRelabel,zRelabel]
  have hlcj := renameInto hlc j Theta hj
  have hrcj := renameInto hrc j Theta hj
  have ihj := renameInto ih j Theta hj
  rw [graph2Rename] at hlcj hrcj
  rw [belowRawRename] at ihj
  obtain ⟨hp,hr⟩ := QueriesProof.unaryRecover (base.relabel j) (dest.relabel j) ys hq
  exact atChildren n arity (left.relabel j) (right.relabel j) (f.relabel j) (g.relabel j)
    (base.relabel j) (dest.relabel j) (node.relabel j) (rev.relabel j) (window.relabel j)
    (symbols.relabel j) (types.relabel j) (ys 0) (ys 1) hlcj hrcj (h.rename j Theta hj) ihj hp hr

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeSymmetry.OrdinaryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeSymmetry.OrdinaryProof
