module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.BoundTransportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.PairScalarProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.NilValueProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.ValueProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.BoundsMeasureProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof (refl symm)
open InternalControlGraphSupportProof (valueUnique)
open InternalControlGraphSupportProof (outputTransport)
open InternalApplicationStepPeelSupportProof (andIntro)
open Continuation20261115
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem measuredSize (n : Nat) (raw pair size label canonical knownSize knownLabel : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) pair raw)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing pair size label)))
    (hc : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) canonical raw)))
    (hk : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing canonical knownSize knownLabel))) :
    Nonempty (Derivation body Delta (eqn size knownSize)) := by
  obtain ⟨he⟩ := valueUnique (OriginalCodeBoundsRecursion.bounds n) pair canonical ![raw] hb hc
  have hp' := outputTransport InternalPairing.pairing canonical pair ![knownSize,knownLabel] ⟨symm he⟩ hk
  exact OriginalTypedEnumerationDepthBound.PairScalarProof.sizeUnique pair size label knownSize knownLabel hp hp'

theorem measuredLabel (n : Nat) (raw pair size label canonical knownSize knownLabel : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) pair raw)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing pair size label)))
    (hc : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) canonical raw)))
    (hk : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing canonical knownSize knownLabel))) :
    Nonempty (Derivation body Delta (eqn label knownLabel)) := by
  obtain ⟨he⟩ := valueUnique (OriginalCodeBoundsRecursion.bounds n) pair canonical ![raw] hb hc
  have hp' := outputTransport InternalPairing.pairing canonical pair ![knownSize,knownLabel] ⟨symm he⟩ hk
  exact OriginalTypedEnumerationDepthBound.PairScalarProof.labelUnique pair size label knownSize knownLabel hp hp'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.BoundsMeasureProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.BoundsMeasureProof
