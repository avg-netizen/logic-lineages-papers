module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.UnaryBoundsCongruenceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.BinaryQueriesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankUnaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankConsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankNumberedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.BinaryBoundsCongruenceProof
open Continuation20261114 Continuation20261115 Continuation20261116
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261115.OriginalBoundsRecombination (maximum merge)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalTagArithmeticSyntaxProof (z suc eqn sucRelabel zRelabel eqnRelabel)
open InternalTagArithmeticSupportProof (trans symm)
open Continuation20261115
open OriginalCodeBoundsConstructors.BinaryRootProof (constructor)

theorem sameChildValues (cons : Bool) (n : Nat)
    (left right lm rm lc ld rc rd first second lv rv : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (graph3 (constructor cons) left lm lc ld)))
    (hrc : Nonempty (Derivation body Delta (graph3 (constructor cons) right rm rc rd)))
    (hlg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) left)))
    (hrg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) right)))
    (hlfirst : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankRaw first lc)))
    (hrfirst : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankRaw first rc)))
    (hlsecond : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankRaw second ld)))
    (hrsecond : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankRaw second rd)))
    (hlv : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankRaw lv left)))
    (hrv : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankRaw rv right)))
    : Nonempty (Derivation body Delta (eqn lv rv)) := by
  have hl : Nonempty (Derivation body Delta (graph2 OriginalRawVariableRank.rankSum lv lc ld)) := by
    cases cons
    · exact OriginalRawVariableRankApplicationProof.rankApplicationForward left lv lm lc ld hlc hlv
    · exact OriginalRawVariableRankConsProof.rankConsForward left lv lm lc ld hlc hlv
  have hr : Nonempty (Derivation body Delta (graph2 OriginalRawVariableRank.rankSum rv rc rd)) := by
    cases cons
    · exact OriginalRawVariableRankApplicationProof.rankApplicationForward right rv rm rc rd hrc hrv
    · exact OriginalRawVariableRankConsProof.rankConsForward right rv rm rc rd hrc hrv
  have hla := OriginalRawVariableRankSupportProof.rankSumForward lv lc ld first second hlfirst hlsecond hl
  have hra := OriginalRawVariableRankSupportProof.rankSumForward rv rc rd first second hrfirst hrsecond hr
  exact valueUnique InternalArithmeticPrograms.addition lv rv ![first,second] hla hra

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.BinaryBoundsCongruenceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.BinaryBoundsCongruenceProof
