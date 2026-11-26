module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.BinaryBoundsCongruenceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.UnaryExchangeAtProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.BinaryExchangeAtProof
open Continuation20261114 Continuation20261115 Continuation20261116
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261115.OriginalBoundsRecombination (maximum merge)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open ExchangeInduction ExchangeInductionBindingProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof (symm)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open Continuation20261115
open OriginalCodeBoundsConstructors.BinaryRootProof (constructor)

theorem atValues (cons side : Bool) (n : Nat) (arity : Fin n → Nat)
    (left right lm rm lc ld rc rd child window cv dv other lv rv : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (graph3 (constructor cons) left lm lc ld)))
    (hrc : Nonempty (Derivation body Delta (graph3 (constructor cons) right rm rc rd)))
    (hlg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) left)))
    (hrg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) right)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing child (if side then ld else lc) (if side then rd else rc))))
    (he : Nonempty (Derivation body Delta (graph2 (OriginalDecodedExchangeEquation.exchange n arity) (suc z) child window)))
    (hcv : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankRaw cv (if side then ld else lc))))
    (hdv : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankRaw dv (if side then rd else rc))))
    (hlo : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankRaw other (if side then lc else ld))))
    (hro : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankRaw other (if side then rc else rd))))
    (hlv : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankRaw lv left)))
    (hrv : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankRaw rv right)))
    (ih : Nonempty (Derivation body Delta (BelowRaw n arity left))) :
    Nonempty (Derivation body Delta (eqn lv rv)) := by
  have hsmall : Nonempty (Derivation body Delta (InternalLessThan.strictLess (if side then ld else lc) left)) := by
    have hs : Nonempty (Derivation body Delta
        (InternalLessThan.strictLess lc left ⊓ InternalLessThan.strictLess ld left)) := by
      cases cons
      · exact OriginalTypedEnumerationDepthBound.DescentProof.application left lm lc ld hlc
      · exact OriginalTypedEnumerationDepthBound.DescentProof.cons left lm lc ld hlc
    cases side
    · exact andLeft hs
    · exact andRight hs
  obtain ⟨heq⟩ := belowRawApply n arity left (if side then ld else lc) (if side then rd else rc) child window cv dv ih hsmall
    (andIntro hp (andIntro he (andIntro hcv hdv)))
  have hdv' := outputTransport OriginalRawSyntaxTransport.variableRankRaw dv cv ![if side then rd else rc] ⟨symm heq⟩ hdv
  cases side
  · exact BinaryBoundsCongruenceProof.sameChildValues cons n left right lm rm lc ld rc rd cv other lv rv
      hlc hrc hlg hrg hcv hdv' hlo hro hlv hrv
  · exact BinaryBoundsCongruenceProof.sameChildValues cons n left right lm rm lc ld rc rd other cv lv rv
      hlc hrc hlg hrg hlo hro hcv hdv' hlv hrv
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.BinaryExchangeAtProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.BinaryExchangeAtProof
