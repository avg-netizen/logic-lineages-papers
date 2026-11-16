module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.BoundTransportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.PairScalarProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.NilValueProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.ValueProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.LeafMeasureProof
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
  exact PairScalarProof.sizeUnique pair size label knownSize knownLabel hp hp'

theorem measuredDepth (n : Nat) (raw depth : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) raw)))
    (hd : Nonempty (Derivation body Delta (graph1 (OriginalEnumerationDepth.depth n) depth raw)))
    (hchildren : Nonempty (Derivation body Delta (graph2 OriginalEnumerationDepth.dependency z raw z))) :
    Nonempty (Derivation body Delta (eqn depth (suc z))) :=
  valueUnique (OriginalEnumerationDepth.depth n) depth (suc z) ![raw] hd
    (OriginalEnumerationDepth.ValueProof.leaf n raw hg hchildren)

theorem termResult (size depth : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (eqn size (suc z))))
    (hd : Nonempty (Derivation body Delta (eqn depth (suc z)))) :
    Nonempty (Derivation body Delta
      (termBound depth size ⊓ InternalLessThan.strictLess z size)) :=
  andIntro (BoundTransportProof.termTransport depth size (suc z) (suc z) hd hs BoundTransportProof.unitBound)
    (InternalOriginalPairingOrderArithmeticProof.strictTransport z size z (suc z)
      ⟨refl _⟩ hs (ArithmeticProof.positiveSuccessor z))

theorem argumentsResult (size depth : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (eqn size z)))
    (hd : Nonempty (Derivation body Delta (eqn depth (suc z)))) :
    Nonempty (Derivation body Delta (argumentsBound depth size)) :=
  BoundTransportProof.argumentsTransport depth size (suc z) z hd hs BoundTransportProof.nilBound
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.LeafMeasureProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.LeafMeasureProof
