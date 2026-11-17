module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalInstalledEdgeReversal.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalConcreteStructuralEdge.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedRank.SupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.WindowSourceHeadInclusion.ClosureSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalInstalledEdgeReversal.PairTransportProof
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
theorem rightInput (window symbols left right : OTerm alpha)
 (he : Nonempty (Derivation body Delta (eqn left right)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing window symbols left))) :
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing window symbols right)) := by
 unfold graph2 programGraph at hp ⊢
 apply InternalGraphCompositionEqualityProof.graphInputTransport body alpha 2 Delta
   (OrdinaryArithmetic.graphFormula InternalPairing.pairing) window
   ![symbols,left] ![symbols,right] _ hp
 intro i
 refine Fin.cases ?_ (fun i => ?_) i
 · rw [InternalSourceInversionSupportProof.onEquality]
   exact ⟨InternalTagArithmeticSupportProof.refl _⟩
 · refine Fin.cases ?_ (fun i => Fin.elim0 i) i
   rw [InternalSourceInversionSupportProof.onEquality]
   exact he

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalInstalledEdgeReversal.PairTransportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalInstalledEdgeReversal.PairTransportProof
