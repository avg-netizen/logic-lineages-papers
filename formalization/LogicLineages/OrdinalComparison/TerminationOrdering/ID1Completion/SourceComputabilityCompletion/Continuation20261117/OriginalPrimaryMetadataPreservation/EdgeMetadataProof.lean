module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMetadataPreservation.EdgeMetadataContextProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedRank.SupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMetadataPreservation.EdgeMetadataProof
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
 (source target parameter sourceType sourceRaw targetType targetRaw sourceBounds targetBounds : OTerm alpha)
 (hs : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing source sourceType sourceRaw)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing target targetType targetRaw)))
 (hl : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) sourceBounds sourceRaw)))
 (hr : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) targetBounds targetRaw)))
 (he : Nonempty (Derivation body Delta (graph3 (OriginalConcreteStructuralEdge.edge n arity) (numeral 1) source target parameter)))
 : Nonempty (Derivation body Delta (eqn sourceType targetType ⊓ eqn sourceBounds targetBounds)) := by
 apply OriginalDecodedRank.SupportProof.pairCases parameter _
 intro beta j Theta context gamma hj hnew
 simp only [conjunctionRename,eqnRelabel]
 have hs' := renameInto hs j Theta hj
 simp only [graph2Rename,numeral,sucRelabel,zRelabel] at hs'
 have ht' := renameInto ht j Theta hj
 simp only [graph2Rename,numeral,sucRelabel,zRelabel] at ht'
 have hl' := renameInto hl j Theta hj
 simp only [graph1Rename,numeral,sucRelabel,zRelabel] at hl'
 have hr' := renameInto hr j Theta hj
 simp only [graph1Rename,numeral,sucRelabel,zRelabel] at hr'
 have he' := renameInto he j Theta hj
 simp only [graph3Rename,numeral,sucRelabel,zRelabel] at he'
 exact EdgeMetadataContextProof.preserved n arity
  (source.relabel j) (target.relabel j) (parameter.relabel j) (sourceType.relabel j) (sourceRaw.relabel j) (targetType.relabel j) (targetRaw.relabel j) (sourceBounds.relabel j) (targetBounds.relabel j) context gamma
  hs' ht' hl' hr' he' hnew

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMetadataPreservation.EdgeMetadataProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMetadataPreservation.EdgeMetadataProof
