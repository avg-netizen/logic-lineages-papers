module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeSymmetry.QueriesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedBinaryRecurrence.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.DescentProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.BinaryRootProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeSymmetry.BinaryProof
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
open OriginalCodeBoundsConstructors.BinaryRootProof (constructor)
theorem atChildren (cons : Bool) (n : Nat) (arity : Fin n → Nat)
    (left right lm rm lc ld rc rd node rev window symbols types first rfirst last rlast : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (graph3 (constructor cons) left lm lc ld)))
    (hrc : Nonempty (Derivation body Delta (graph3 (constructor cons) right rm rc rd)))
    (h : Facts (body := body) (Delta := Delta) n arity left right node rev window symbols types)
    (ih : Nonempty (Derivation body Delta (BelowRaw n arity left)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing first lc rc)))
    (hrp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rfirst rc lc)))
    (hq : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing last ld rd)))
    (hrq : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rlast rd ld))) :
    Nonempty (Derivation body Delta (graph2 (OriginalDecodedExchangeEquation.exchange n arity) (suc z) rev window)) := by
  have hf := (OriginalDecodedBinaryRecurrence.Proof.binaryRecurrence n arity body alpha Delta cons
    left right lm rm lc ld rc rd node first last window hlc hrc h.pair hp hq).mp h.exchange
  have small : Nonempty (Derivation body Delta
      (InternalLessThan.strictLess lc left ⊓ InternalLessThan.strictLess ld left)) := by
    cases cons
    · exact OriginalTypedEnumerationDepthBound.DescentProof.application left lm lc ld hlc
    · exact OriginalTypedEnumerationDepthBound.DescentProof.cons left lm lc ld hlc
  apply (OriginalDecodedBinaryRecurrence.Proof.binaryRecurrence n arity body alpha Delta cons
    right left rm lm rc rd lc ld rev rfirst rlast window hrc hlc h.reversePair hrp hrq).mpr
  apply andIntro (reverseGuard h)
  obtain ⟨hmeta⟩ := andLeft (andRight hf)
  apply andIntro ⟨symm hmeta⟩
  apply orCases (andRight (andRight hf))
  · intro Theta hi hb
    obtain ⟨heq⟩ := andLeft hb
    have hh := childReverse left lc rc first rfirst window symbols types
      (weakenProof ih hi) (weakenProof (andLeft small) hi) (weakenProof hp hi) (weakenProof hrp hi)
      (weakenProof h.windowPair hi) (weakenProof h.closed hi) (andRight hb)
    obtain ⟨ha⟩ := andIntro ⟨symm heq⟩ hh
    exact ⟨orLeft ha⟩
  · intro Theta hi hb
    obtain ⟨heq⟩ := andLeft hb
    have hh := childReverse left ld rd last rlast window symbols types
      (weakenProof ih hi) (weakenProof (andRight small) hi) (weakenProof hq hi) (weakenProof hrq hi)
      (weakenProof h.windowPair hi) (weakenProof h.closed hi) (andRight hb)
    obtain ⟨ha⟩ := andIntro ⟨symm heq⟩ hh
    exact ⟨orRight ha⟩

theorem reversed (cons : Bool) (n : Nat) (arity : Fin n → Nat)
    (left right lm rm lc ld rc rd node rev window symbols types : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (graph3 (constructor cons) left lm lc ld)))
    (hrc : Nonempty (Derivation body Delta (graph3 (constructor cons) right rm rc rd)))
    (h : Facts (body := body) (Delta := Delta) n arity left right node rev window symbols types)
    (ih : Nonempty (Derivation body Delta (BelowRaw n arity left))) :
    Nonempty (Derivation body Delta (graph2 (OriginalDecodedExchangeEquation.exchange n arity) (suc z) rev window)) := by
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases QueriesProof.binary ![lc,ld,rc,rd] _
  intro beta j ys Theta hj hq
  rw [QueriesProof.vector4Rename] at hq
  simp only [graph2Rename,sucRelabel,zRelabel]
  have hlcj := renameInto hlc j Theta hj
  have hrcj := renameInto hrc j Theta hj
  have ihj := renameInto ih j Theta hj
  rw [graph3Rename] at hlcj hrcj
  rw [belowRawRename] at ihj
  obtain ⟨hp,hr,hq,hs⟩ := QueriesProof.binaryRecover (lc.relabel j) (ld.relabel j) (rc.relabel j) (rd.relabel j) ys hq
  exact atChildren cons n arity (left.relabel j) (right.relabel j) (lm.relabel j) (rm.relabel j)
    (lc.relabel j) (ld.relabel j) (rc.relabel j) (rd.relabel j) (node.relabel j) (rev.relabel j) (window.relabel j)
    (symbols.relabel j) (types.relabel j) (ys 0) (ys 1) (ys 2) (ys 3) hlcj hrcj (h.rename j Theta hj) ihj hp hr hq hs

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeSymmetry.BinaryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeSymmetry.BinaryProof
