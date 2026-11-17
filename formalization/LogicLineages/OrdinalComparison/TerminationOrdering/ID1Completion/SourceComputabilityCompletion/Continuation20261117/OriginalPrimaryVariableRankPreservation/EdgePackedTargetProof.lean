module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryVariableRankPreservation.EdgePackedFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedRank.SupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryVariableRankPreservation.EdgePackedTargetProof
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
 (source target parameter sourceRank targetRank sourceType sourceRaw : OTerm alpha)
 (hs : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing source sourceType sourceRaw)))
 (hl : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw sourceRank source)))
 (hr : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw targetRank target)))
 (he : Nonempty (Derivation body Delta (graph3 (OriginalConcreteStructuralEdge.edge n arity) (numeral 1) source target parameter))) :
 Nonempty (Derivation body Delta (eqn sourceRank targetRank)) := by
 apply OriginalDecodedRank.SupportProof.pairCases target _
 intro beta j Theta targetType targetRaw hj hp
 rw [eqnRelabel]
 have hs' := renameInto hs j Theta hj
 simp only [graph1Rename,graph2Rename,graph3Rename,numeral,sucRelabel,zRelabel] at hs'
 have hl' := renameInto hl j Theta hj
 simp only [graph1Rename,graph2Rename,graph3Rename,numeral,sucRelabel,zRelabel] at hl'
 have hr' := renameInto hr j Theta hj
 simp only [graph1Rename,graph2Rename,graph3Rename,numeral,sucRelabel,zRelabel] at hr'
 have he' := renameInto he j Theta hj
 simp only [graph1Rename,graph2Rename,graph3Rename,numeral,sucRelabel,zRelabel] at he'
 exact EdgePackedFieldsProof.preserved n arity (source.relabel j) (target.relabel j) (parameter.relabel j) (sourceType.relabel j) (sourceRaw.relabel j) targetType targetRaw (sourceRank.relabel j) (targetRank.relabel j) hs' hp hl' hr' he'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryVariableRankPreservation.EdgePackedTargetProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryVariableRankPreservation.EdgePackedTargetProof
