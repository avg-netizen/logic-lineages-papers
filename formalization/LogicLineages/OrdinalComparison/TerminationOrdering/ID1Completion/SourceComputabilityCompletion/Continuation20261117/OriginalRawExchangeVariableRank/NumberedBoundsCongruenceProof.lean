module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.UnaryBoundsCongruenceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.NumberedQueriesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.NumberedValueProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.BinaryValueProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankUnaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankConsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankNumberedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.NumberedBoundsCongruenceProof
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
open OriginalRawSyntaxTransport

theorem sameChildValues (n : Nat)
    (left right label lh rh lt rt lts rts lc ld rc rd first second lv rv : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (programGraph numberedConstructor left ![label,lh,lt,lc,lts,ld])))
    (hrc : Nonempty (Derivation body Delta (programGraph numberedConstructor right ![label,rh,rt,rc,rts,rd])))
    (hlg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) left)))
    (hrg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) right)))
    (hlfirst : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankRaw first lc)))
    (hrfirst : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankRaw first rc)))
    (hlsecond : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankRaw second ld)))
    (hrsecond : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankRaw second rd)))
    (hlv : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankRaw lv left)))
    (hrv : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankRaw rv right)))
    : Nonempty (Derivation body Delta (eqn lv rv)) := by
  have hl := OriginalRawVariableRankNumberedProof.rankNumberedForward left lv label lh lt lc lts ld hlc hlv
  have hr := OriginalRawVariableRankNumberedProof.rankNumberedForward right rv label rh rt rc rts rd hrc hrv
  have hla := OriginalRawVariableRankSupportProof.rankSumForward lv lc ld first second hlfirst hlsecond hl
  have hra := OriginalRawVariableRankSupportProof.rankSumForward rv rc rd first second hrfirst hrsecond hr
  exact valueUnique InternalArithmeticPrograms.addition lv rv ![first,second] hla hra

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.NumberedBoundsCongruenceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.NumberedBoundsCongruenceProof
