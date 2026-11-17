module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalInstalledEdgeReversal.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalConcreteStructuralEdge.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedRank.SupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.WindowSourceHeadInclusion.ClosureSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalInstalledEdgeReversal.TargetProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalInstalledEdgeReversal.SourceProof
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
 (source target parameter context gamma types : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter context gamma)))
 (hq : Nonempty (Derivation body Delta (graph1 OriginalUniverseDomainCoverage.contextTypes types context)))
 (ha : Nonempty (Derivation body Delta (WindowSourceHeadInclusion.ArrowClosed types)))
 (he : Nonempty (Derivation body Delta (graph3 (OriginalConcreteStructuralEdge.edge n arity) (numeral 1) source target parameter)))
: Nonempty (Derivation body Delta (graph3 (OriginalConcreteStructuralEdge.edge n arity) (numeral 1) target source parameter)) := by
 apply OriginalDecodedRank.SupportProof.pairCases source _
 intro beta j Theta sourceType sourceRaw hj hnew
 simp only [graph1Rename,graph2Rename,graph3Rename,numeral,sucRelabel,zRelabel,closureRename]
 have hp' := renameInto hp j Theta hj
 simp only [graph1Rename,graph2Rename,graph3Rename,numeral,sucRelabel,zRelabel,closureRename] at hp'
 have hq' := renameInto hq j Theta hj
 simp only [graph1Rename,graph2Rename,graph3Rename,numeral,sucRelabel,zRelabel,closureRename] at hq'
 have ha' := renameInto ha j Theta hj
 simp only [graph1Rename,graph2Rename,graph3Rename,numeral,sucRelabel,zRelabel,closureRename] at ha'
 have he' := renameInto he j Theta hj
 simp only [graph1Rename,graph2Rename,graph3Rename,numeral,sucRelabel,zRelabel,closureRename] at he'
 exact TargetProof.reverse n arity (source.relabel j) (target.relabel j) (parameter.relabel j) (context.relabel j) (gamma.relabel j) (types.relabel j) sourceType sourceRaw
  hp' hq' ha' he' hnew

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalInstalledEdgeReversal.SourceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalInstalledEdgeReversal.SourceProof
