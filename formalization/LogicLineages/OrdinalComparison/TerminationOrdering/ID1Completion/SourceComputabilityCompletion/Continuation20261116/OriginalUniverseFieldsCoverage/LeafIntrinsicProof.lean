module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.MetadataProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseDomainCoverage.MemberProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.LeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.LeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportLeafAcceptanceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.LeafMeasureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.TypesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.LeafIntrinsicProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open OriginalUniverseDecoderInternalAcceptance
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open TwoSol20261113.CalibratedPrimary.Membership (contains)

theorem variableCode (n : Nat) (raw field pair size label : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableConstructor raw field)))
    (hb : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) pair raw)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing pair size label))) :
    Nonempty (Derivation body Delta
      (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) raw ⊓ InternalLessThan.strictLess z size)) := by
  have hg := OriginalEnumerationValidity.LeafProof.variableValid n raw field hc
  have hk := InternalApplicationValidityStackAppendTransitionProof.pairOneZero
    (body := body) (Gamma := Delta) (α := alpha)
  have hv := OriginalCodeBoundsConstructors.LeafValueProof.variableValue n raw field (suc (suc z)) hc hg hk
  have hs := OriginalTypedEnumerationDepthBound.LeafMeasureProof.measuredSize n raw pair size label
    (suc (suc z)) (suc z) z hb hp hv hk
  exact andIntro hg (InternalOriginalPairingOrderArithmeticProof.strictTransport z size z (suc z)
    ⟨refl _⟩ hs (OriginalTypedEnumerationDepthBound.ArithmeticProof.positiveSuccessor z))

theorem bottom (n : Nat) (raw field pair size label : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.bottomConstructor raw field)))
    (hb : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) pair raw)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing pair size label))) :
    Nonempty (Derivation body Delta
      (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) raw ⊓ InternalLessThan.strictLess z size)) := by
  have hg := OriginalEnumerationValidity.LeafProof.bottom n raw field hc
  have hk := InternalApplicationValidityStackAppendTransitionProof.pairOneZero
    (body := body) (Gamma := Delta) (α := alpha)
  have hv := OriginalCodeBoundsConstructors.LeafValueProof.bottomValue n raw field (suc (suc z)) hc hg hk
  have hs := OriginalTypedEnumerationDepthBound.LeafMeasureProof.measuredSize n raw pair size label
    (suc (suc z)) (suc z) z hb hp hv hk
  exact andIntro hg (InternalOriginalPairingOrderArithmeticProof.strictTransport z size z (suc z)
    ⟨refl _⟩ hs (OriginalTypedEnumerationDepthBound.ArithmeticProof.positiveSuccessor z))

theorem nilCode (n : Nat) (arity : Fin n → Nat) (H : Program 1)
    (raw typ gamma context types size : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.nilConstructor raw Fin.elim0)))
    (ha : Nonempty (Derivation body Delta (ArgumentsAccepted H (OriginalUniverseDomainCoverage.member n)
      (OriginalGuardedHeadSourceCoverage.window n arity) typ raw gamma context))) :
    Nonempty (Derivation body Delta
      (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) raw ⊓ OriginalEnumerationFields.Targets.typesAllowed typ types size)) := by
  have hi := OriginalUniverseDecoderTransportLeafAcceptanceProof.nilIff H (OriginalUniverseDomainCoverage.member n)
    (OriginalGuardedHeadSourceCoverage.window n arity) raw typ gamma context hc
  have hp := Derivation.implicationElimination (Classical.choice (andLeft hi)) (Classical.choice ha)
  have he : Nonempty (Derivation body Delta (equal typ z)) := ⟨Derivation.conjunctionRight hp⟩
  rw [InternalControlGraphSupportProof.equalEqn] at he
  exact andIntro (OriginalEnumerationValidity.LeafProof.nil n raw hc) (TypesProof.empty typ types size he)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.LeafIntrinsicProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.LeafIntrinsicProof
