module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.UnaryBoundsQueriesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankUnaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankConsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankNumberedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.UnaryBoundsCongruenceProof
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
open OriginalCodeBoundsConstructors.UnaryValueProof (constructor)

theorem sameChildValue (ordinary : Bool) (n : Nat) (left right lm rm lc rc value lv rv : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (graph2 (constructor ordinary) left lm lc)))
    (hrc : Nonempty (Derivation body Delta (graph2 (constructor ordinary) right rm rc)))
    (hlg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) left)))
    (hrg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) right)))
    (hlch : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankRaw value lc)))
    (hrch : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankRaw value rc)))
    (hlv : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankRaw lv left)))
    (hrv : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankRaw rv right))) :
    Nonempty (Derivation body Delta (eqn lv rv)) := by
  have hl : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankRaw value left)) := by
    cases ordinary
    · exact OriginalRawVariableRankUnaryProof.rankLambdaBackward left value lm lc hlc hlch
    · exact OriginalRawVariableRankUnaryProof.rankOrdinaryBackward left value lm lc hlc hlch
  have hr : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankRaw value right)) := by
    cases ordinary
    · exact OriginalRawVariableRankUnaryProof.rankLambdaBackward right value rm rc hrc hrch
    · exact OriginalRawVariableRankUnaryProof.rankOrdinaryBackward right value rm rc hrc hrch
  obtain ⟨hel⟩ := valueUnique OriginalRawSyntaxTransport.variableRankRaw lv value ![left] hlv hl
  obtain ⟨her⟩ := valueUnique OriginalRawSyntaxTransport.variableRankRaw rv value ![right] hrv hr
  exact ⟨trans hel (symm her)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.UnaryBoundsCongruenceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.UnaryBoundsCongruenceProof
