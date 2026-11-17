module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalConcreteStructuralEdge.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.Proof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryVariableRankPreservation.EdgeRankAtFieldsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (eqn eqnRelabel sucRelabel zRelabel)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115 Continuation20261116
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
theorem preserved (n : Nat) (arity : Fin n → Nat)
 (source target parameter sourceType sourceRaw targetType targetRaw sourceRank targetRank context gamma window table node : OTerm alpha)
 (hs : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing source sourceType sourceRaw)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing target targetType targetRaw)))
 (hl : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankRaw sourceRank sourceRaw)))
 (hr : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankRaw targetRank targetRaw)))
 (he : Nonempty (Derivation body Delta (graph3 (OriginalConcreteStructuralEdge.edge n arity) (numeral 1) source target parameter)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter context gamma)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing context window table)))
 (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node sourceRaw targetRaw)))
 : Nonempty (Derivation body Delta (eqn sourceRank targetRank)) := by
 have hf := (OriginalConcreteStructuralEdge.Proof.internalEdge n arity body alpha Delta
   source target parameter sourceType sourceRaw targetType targetRaw context gamma hs ht hp).mp he
 have hguards := andRight (andLeft (andRight hf))
 have hcodeL := andLeft hguards
 have hcodeR := andRight hguards
 have hcall := andRight (andRight hf)
 have hex := (OriginalConcreteStructuralEdge.SupportProof.atContextFactor n arity
   sourceRaw targetRaw context window table node (numeral 1) hc hn).mp hcall
 exact OriginalRawExchangeVariableRank.Proof.rawExchangeVariableRank n arity body alpha Delta
   sourceRaw targetRaw node window sourceRank targetRank hn hcodeL hcodeR hex hl hr

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryVariableRankPreservation.EdgeRankAtFieldsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryVariableRankPreservation.EdgeRankAtFieldsProof
