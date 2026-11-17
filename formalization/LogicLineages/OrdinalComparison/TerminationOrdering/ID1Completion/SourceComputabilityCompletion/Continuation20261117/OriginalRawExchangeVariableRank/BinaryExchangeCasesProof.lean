module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.BinaryExchangeAtProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.ExchangeGuardProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedBinaryRecurrence.Proof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.BinaryExchangeCasesProof
open Continuation20261114 Continuation20261115 Continuation20261116
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261115.OriginalBoundsRecombination (maximum merge)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open ExchangeInduction
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open Continuation20261115
open OriginalCodeBoundsConstructors.BinaryRootProof (constructor)

theorem atValues (cons : Bool) (n : Nat) (arity : Fin n → Nat)
    (left right lm rm lc ld rc rd node first last window cv dv ev fv lv rv : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (graph3 (constructor cons) left lm lc ld)))
    (hrc : Nonempty (Derivation body Delta (graph3 (constructor cons) right rm rc rd)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node left right)))
    (hfirst : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing first lc rc)))
    (hlast : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing last ld rd)))
    (he : Nonempty (Derivation body Delta (graph2 (OriginalDecodedExchangeEquation.exchange n arity) (suc z) node window)))
    (hcv : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankRaw cv lc)))
    (hdv : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankRaw dv rc)))
    (hev : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankRaw ev ld)))
    (hfv : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankRaw fv rd)))
    (hlv : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankRaw lv left)))
    (hrv : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankRaw rv right)))
    (ih : Nonempty (Derivation body Delta (BelowRaw n arity left))) :
    Nonempty (Derivation body Delta (eqn lv rv)) := by
  have hg := Continuation20261116.OriginalExchangeBoundsPreservation.ExchangeGuardProof.accepted n arity node left right window hp he
  have hlg := andLeft hg
  have hrg := andRight hg
  have hr := (OriginalDecodedBinaryRecurrence.Proof.binaryRecurrence n arity body alpha Delta cons
    left right lm rm lc ld rc rd node first last window hlc hrc hp hfirst hlast).mp he
  apply OriginalTypedDecoderInternalBranchProof.orCases (andRight (andRight hr))
  · have hb : Nonempty (Derivation body ((eqn ld rd ⊓ graph2 (OriginalDecodedExchangeEquation.exchange n arity) (suc z) first window) :: Delta)
        (eqn ld rd ⊓ graph2 (OriginalDecodedExchangeEquation.exchange n arity) (suc z) first window)) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have ho := headTransport OriginalRawSyntaxTransport.variableRankRaw ev ld rd (fun i : Fin 0 => Fin.elim0 i)
      (andLeft hb) (withHyp hev _)
    exact BinaryExchangeAtProof.atValues cons false n arity left right lm rm lc ld rc rd first window cv dv ev lv rv
      (withHyp hlc _) (withHyp hrc _) (withHyp hlg _) (withHyp hrg _) (withHyp hfirst _)
      (andRight hb) (withHyp hcv _) (withHyp hdv _) (withHyp hev _) ho
      (withHyp hlv _) (withHyp hrv _) (withHyp ih _)
  · have hb : Nonempty (Derivation body ((eqn lc rc ⊓ graph2 (OriginalDecodedExchangeEquation.exchange n arity) (suc z) last window) :: Delta)
        (eqn lc rc ⊓ graph2 (OriginalDecodedExchangeEquation.exchange n arity) (suc z) last window)) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have ho := headTransport OriginalRawSyntaxTransport.variableRankRaw cv lc rc (fun i : Fin 0 => Fin.elim0 i)
      (andLeft hb) (withHyp hcv _)
    exact BinaryExchangeAtProof.atValues cons true n arity left right lm rm lc ld rc rd last window ev fv cv lv rv
      (withHyp hlc _) (withHyp hrc _) (withHyp hlg _) (withHyp hrg _) (withHyp hlast _)
      (andRight hb) (withHyp hev _) (withHyp hfv _) (withHyp hcv _) ho
      (withHyp hlv _) (withHyp hrv _) (withHyp ih _)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.BinaryExchangeCasesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.BinaryExchangeCasesProof
