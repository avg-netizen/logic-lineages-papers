module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeSymmetry.QueriesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedLambdaRecurrence.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.DescentProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeSymmetry.LambdaProof
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
theorem atChildren (n : Nat) (arity : Fin n → Nat)
    (left right lm rm lc rc node rev window symbols types child reversed : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.lambdaConstructor left lm lc)))
    (hrc : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.lambdaConstructor right rm rc)))
    (h : Facts (body := body) (Delta := Delta) n arity left right node rev window symbols types)
    (ih : Nonempty (Derivation body Delta (BelowRaw n arity left)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing child lc rc)))
    (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing reversed rc lc))) :
    Nonempty (Derivation body Delta (graph2 (OriginalDecodedExchangeEquation.exchange n arity) (suc z) rev window)) := by
  have hf := (OriginalDecodedLambdaRecurrence.Proof.lambdaRecurrence n arity body alpha Delta
    left right lm rm lc rc node child window hlc hrc h.pair hp).mp h.exchange
  have small := OriginalTypedEnumerationDepthBound.DescentProof.lambdaCode left lm lc hlc
  have hi := childReverse left lc rc child reversed window symbols types ih small hp hr h.windowPair h.closed
    (andRight (andRight hf))
  obtain ⟨heq⟩ := andLeft (andRight hf)
  exact (OriginalDecodedLambdaRecurrence.Proof.lambdaRecurrence n arity body alpha Delta
    right left rm lm rc lc rev reversed window hrc hlc h.reversePair hr).mpr
    (andIntro (reverseGuard h) (andIntro ⟨symm heq⟩ hi))

theorem reversed (n : Nat) (arity : Fin n → Nat)
    (left right lm rm lc rc node rev window symbols types : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.lambdaConstructor left lm lc)))
    (hrc : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.lambdaConstructor right rm rc)))
    (h : Facts (body := body) (Delta := Delta) n arity left right node rev window symbols types)
    (ih : Nonempty (Derivation body Delta (BelowRaw n arity left))) :
    Nonempty (Derivation body Delta (graph2 (OriginalDecodedExchangeEquation.exchange n arity) (suc z) rev window)) := by
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases QueriesProof.unary ![lc,rc] _
  intro beta j ys Theta hj hq
  rw [QueriesProof.vector2Rename] at hq
  simp only [graph2Rename,sucRelabel,zRelabel]
  have hlcj := renameInto hlc j Theta hj
  have hrcj := renameInto hrc j Theta hj
  have ihj := renameInto ih j Theta hj
  rw [graph2Rename] at hlcj hrcj
  rw [belowRawRename] at ihj
  obtain ⟨hp,hr⟩ := QueriesProof.unaryRecover (lc.relabel j) (rc.relabel j) ys hq
  exact atChildren n arity (left.relabel j) (right.relabel j) (lm.relabel j) (rm.relabel j)
    (lc.relabel j) (rc.relabel j) (node.relabel j) (rev.relabel j) (window.relabel j)
    (symbols.relabel j) (types.relabel j) (ys 0) (ys 1) hlcj hrcj (h.rename j Theta hj) ihj hp hr

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeSymmetry.LambdaProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeSymmetry.LambdaProof
