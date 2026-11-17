module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalInstalledEdgeReversal.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalConcreteStructuralEdge.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedRank.SupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.WindowSourceHeadInclusion.ClosureSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalInstalledEdgeReversal.WindowFieldsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalInstalledEdgeReversal.WindowProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (eqn sucRelabel zRelabel)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115 Continuation20261116
open WindowSourceHeadInclusion.ClosureSyntaxProof (closureRename)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
theorem reverse (n : Nat) (arity : Fin n → Nat)
 (source target parameter context gamma types sourceType sourceRaw targetType targetRaw window table : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter context gamma)))
 (hq : Nonempty (Derivation body Delta (graph1 OriginalUniverseDomainCoverage.contextTypes types context)))
 (ha : Nonempty (Derivation body Delta (WindowSourceHeadInclusion.ArrowClosed types)))
 (he : Nonempty (Derivation body Delta (graph3 (OriginalConcreteStructuralEdge.edge n arity) (numeral 1) source target parameter)))
 (hs : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing source sourceType sourceRaw)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing target targetType targetRaw)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing context window table)))
: Nonempty (Derivation body Delta (graph3 (OriginalConcreteStructuralEdge.edge n arity) (numeral 1) target source parameter)) := by
 apply OriginalDecodedRank.SupportProof.pairCases window _
 intro beta j Theta symbols actualTypes hj hnew
 simp only [graph1Rename,graph2Rename,graph3Rename,numeral,sucRelabel,zRelabel,closureRename]
 have hp' := renameInto hp j Theta hj
 simp only [graph1Rename,graph2Rename,graph3Rename,numeral,sucRelabel,zRelabel,closureRename] at hp'
 have hq' := renameInto hq j Theta hj
 simp only [graph1Rename,graph2Rename,graph3Rename,numeral,sucRelabel,zRelabel,closureRename] at hq'
 have ha' := renameInto ha j Theta hj
 simp only [graph1Rename,graph2Rename,graph3Rename,numeral,sucRelabel,zRelabel,closureRename] at ha'
 have he' := renameInto he j Theta hj
 simp only [graph1Rename,graph2Rename,graph3Rename,numeral,sucRelabel,zRelabel,closureRename] at he'
 have hs' := renameInto hs j Theta hj
 simp only [graph1Rename,graph2Rename,graph3Rename,numeral,sucRelabel,zRelabel,closureRename] at hs'
 have ht' := renameInto ht j Theta hj
 simp only [graph1Rename,graph2Rename,graph3Rename,numeral,sucRelabel,zRelabel,closureRename] at ht'
 have hc' := renameInto hc j Theta hj
 simp only [graph1Rename,graph2Rename,graph3Rename,numeral,sucRelabel,zRelabel,closureRename] at hc'
 exact WindowFieldsProof.reverse n arity (source.relabel j) (target.relabel j) (parameter.relabel j) (context.relabel j) (gamma.relabel j) (types.relabel j) (sourceType.relabel j) (sourceRaw.relabel j) (targetType.relabel j) (targetRaw.relabel j) (window.relabel j) (table.relabel j) symbols actualTypes
  hp' hq' ha' he' hs' ht' hc' hnew

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalInstalledEdgeReversal.WindowProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalInstalledEdgeReversal.WindowProof
