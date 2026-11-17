module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMetadataPreservation.EdgeMetadataAtFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedRank.SupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMetadataPreservation.EdgeMetadataNodeProof
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
 (source target parameter sourceType sourceRaw targetType targetRaw sourceBounds targetBounds context gamma window table : OTerm alpha)
 (hs : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing source sourceType sourceRaw)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing target targetType targetRaw)))
 (hl : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) sourceBounds sourceRaw)))
 (hr : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) targetBounds targetRaw)))
 (he : Nonempty (Derivation body Delta (graph3 (OriginalConcreteStructuralEdge.edge n arity) (numeral 1) source target parameter)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter context gamma)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing context window table)))
 : Nonempty (Derivation body Delta (eqn sourceType targetType ⊓ eqn sourceBounds targetBounds)) := by
 apply InternalAcceptanceSupportProof.programCases InternalPairing.pairing ![sourceRaw,targetRaw] _
 intro beta j Theta node hj hnew
 have hx : (fun i => (![sourceRaw,targetRaw] i).relabel j) = ![sourceRaw.relabel j,targetRaw.relabel j] := by
  funext i; fin_cases i <;> rfl
 rw [hx] at hnew
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
 have hp' := renameInto hp j Theta hj
 simp only [graph2Rename,numeral,sucRelabel,zRelabel] at hp'
 have hc' := renameInto hc j Theta hj
 simp only [graph2Rename,numeral,sucRelabel,zRelabel] at hc'
 exact EdgeMetadataAtFieldsProof.preserved n arity
  (source.relabel j) (target.relabel j) (parameter.relabel j) (sourceType.relabel j) (sourceRaw.relabel j) (targetType.relabel j) (targetRaw.relabel j) (sourceBounds.relabel j) (targetBounds.relabel j) (context.relabel j) (gamma.relabel j) (window.relabel j) (table.relabel j) node
  hs' ht' hl' hr' he' hp' hc' hnew

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMetadataPreservation.EdgeMetadataNodeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMetadataPreservation.EdgeMetadataNodeProof
