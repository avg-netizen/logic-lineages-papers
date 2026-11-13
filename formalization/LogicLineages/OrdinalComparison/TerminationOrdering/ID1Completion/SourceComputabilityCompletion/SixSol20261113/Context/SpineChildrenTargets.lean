module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalScalarSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.SpineChildrenTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open OriginalUniverseDecoderInternalAcceptance
open OriginalTypedDecoderStepSpecification
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Actual original ordinary source gives its BASE argument admission and the
same outer-context guard. All extra premises are actual constructor/field graphs. -/
def ActualOrdinary : Prop := ∀ (H G : Program 1) (M W : Program 2)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (packed parameter typ raw c gamma head base headData result types : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) packed parameter)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed typ raw)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)) →
 Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.ordinaryConstructor raw head base)) →
 Nonempty (Derivation body Delta (graph1 H headData head)) →
 Nonempty (Derivation body Delta (StepArrowFields headData result types)) →
 Nonempty (Derivation body Delta
   (graph1 G (numeral 1) c ⊓ ArgumentsAccepted H M W types base gamma c))

/-- Numbered BASE and extras retain their actual, separate type lists. No sort
or observation equality is required or inferred by this source-only theorem. -/
def ActualNumbered : Prop := ∀ (H G : Program 1) (M W : Program 2)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (packed parameter typ raw c gamma label head recorded base extraTypes extras headData headResult baseTypes : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) packed parameter)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed typ raw)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)) →
 Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor raw ![label,head,recorded,base,extraTypes,extras])) →
 Nonempty (Derivation body Delta (graph1 H headData head)) →
 Nonempty (Derivation body Delta (StepArrowFields headData headResult baseTypes)) →
 Nonempty (Derivation body Delta
   (graph1 G (numeral 1) c ⊓
    (ArgumentsAccepted H M W baseTypes base gamma c ⊓ ArgumentsAccepted H M W extraTypes extras gamma c)))

/-- Original tag7 admission yields an actual packed head source and accepted
tail at the SAME parameter. G(c) is necessary for the source predicate and is
retained by the parent inversions above, not invented from ArgumentsAccepted. -/
def ActualCons : Prop := ∀ (H G : Program 1) (M W : Program 2)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (raw types domain head tail requestedDomain tailTypes packed parameter gamma c : OTerm alpha),
 Nonempty (Derivation body Delta (ArgumentsAccepted H M W types raw gamma c)) →
 Nonempty (Derivation body Delta (graph1 G (numeral 1) c)) →
 Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw domain head tail)) →
 Nonempty (Derivation body Delta (StepArrowFields types requestedDomain tailTypes)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed domain head)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)) →
 Nonempty (Derivation body Delta
   (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) packed parameter ⊓
    ArgumentsAccepted H M W tailTypes tail gamma c))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.SpineChildrenTargets
