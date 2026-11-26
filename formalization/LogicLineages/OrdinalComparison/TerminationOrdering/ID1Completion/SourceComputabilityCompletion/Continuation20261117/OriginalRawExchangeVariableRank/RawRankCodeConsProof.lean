module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.RawRankCodeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankConsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.MergeRecoverProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.RawRankCodeConsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalAcceptanceSupportProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalTagArithmeticSupportProof (refl symm)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115 Continuation20261116
open Continuation20261116.OriginalExchangeBoundsPreservation
open OriginalRawSyntaxTransport (variableRankRaw)
open InternalAcceptanceConjunctionProof (constantZeroValue)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem atRanks (raw typ head tail hv tv out headRank tailRank : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw typ head tail)))
    (hh : Nonempty (Derivation body Delta (graph1 rawRankCode hv head)))
    (ht : Nonempty (Derivation body Delta (graph1 rawRankCode tv tail)))
    (hm : Nonempty (Derivation body Delta (graph2 OriginalBoundsRecombination.merge out hv tv)))
    (hrh : Nonempty (Derivation body Delta (graph1 variableRankRaw headRank head)))
    (hrt : Nonempty (Derivation body Delta (graph1 variableRankRaw tailRank tail))) :
    Nonempty (Derivation body Delta (graph1 rawRankCode out raw)) := by
  have hph := RawRankCodeProof.recover head headRank hv hrh hh
  have hpt := RawRankCodeProof.recover tail tailRank tv hrt ht
  have hp := MergeRecoverProof.pairAtMaximum hv tv headRank z tailRank z z out hph hpt
    (OriginalCodeBoundsConstructors.ZeroMaximumProof.leftZero z) hm
  have hs := OriginalRawVariableRankSupportProof.rankSumBackward (OrdinaryArithmetic.addTerm headRank tailRank)
    head tail headRank tailRank hrh hrt (InternalArithmeticProgramsSupportProof.additionValue headRank tailRank)
  exact RawRankCodeProof.value raw (OrdinaryArithmetic.addTerm headRank tailRank) out
    (OriginalRawVariableRankConsProof.rankConsBackward raw (OrdinaryArithmetic.addTerm headRank tailRank) typ head tail hc hs) hp

theorem cons (n : Nat) (raw typ head tail hv tv out : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw typ head tail)))
    (_hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) raw)))
    (hh : Nonempty (Derivation body Delta (graph1 rawRankCode hv head)))
    (ht : Nonempty (Derivation body Delta (graph1 rawRankCode tv tail)))
    (hm : Nonempty (Derivation body Delta (graph2 OriginalBoundsRecombination.merge out hv tv))) :
    Nonempty (Derivation body Delta (graph1 rawRankCode out raw)) := by
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases
    (fun i : Fin 2 => .composition variableRankRaw (fun _ : Fin 1 => .projection i)) ![head,tail] _
  intro beta j ys Theta hj hq
  have hx : (fun i => (![head,tail] i).relabel j) = ![head.relabel j,tail.relabel j] := by
    funext i; fin_cases i <;> rfl
  rw [hx] at hq
  rw [graph1Rename]
  have hc' := renameInto hc j Theta hj
  have hh' := renameInto hh j Theta hj
  have ht' := renameInto ht j Theta hj
  have hm' := renameInto hm j Theta hj
  rw [graph3Rename] at hc'
  rw [graph1Rename] at hh' ht'
  rw [graph2Rename] at hm'
  exact atRanks (raw.relabel j) (typ.relabel j) (head.relabel j) (tail.relabel j)
    (hv.relabel j) (tv.relabel j) (out.relabel j) (ys 0) (ys 1) hc' hh' ht' hm'
    (unaryRecover variableRankRaw (.projection 0) (ys 0) (head.relabel j) ![head.relabel j,tail.relabel j]
      (hq 0) (projectionValue 0 ![head.relabel j,tail.relabel j]))
    (unaryRecover variableRankRaw (.projection 1) (ys 1) (tail.relabel j) ![head.relabel j,tail.relabel j]
      (hq 1) (projectionValue 1 ![head.relabel j,tail.relabel j]))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.RawRankCodeConsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.RawRankCodeConsProof
