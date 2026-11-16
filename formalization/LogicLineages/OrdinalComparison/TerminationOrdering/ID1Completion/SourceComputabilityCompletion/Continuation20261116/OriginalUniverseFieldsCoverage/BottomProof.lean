module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.MetadataProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseDomainCoverage.MemberProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.LeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.LeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportLeafAcceptanceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.BottomProof
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

theorem atConstructor (n : Nat) (arity : Fin n → Nat) (H : Program 1)
    (seed param raw payload typ gamma context count types heads labels tupleBound : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.bottomConstructor raw payload)))
    (ha : Nonempty (Derivation body Delta (TermAccepted H (OriginalUniverseDomainCoverage.member n)
      (OriginalGuardedHeadSourceCoverage.window n arity) typ raw gamma context)))
    (hcontext : Nonempty (Derivation body Delta (graph2 OriginalClassCodes.context context seed param)))
    (htypes : Nonempty (Derivation body Delta (graph2 OriginalClassCodes.types types seed param))) :
    Nonempty (Derivation body Delta (OriginalEnumerationFields.Targets.accepted n raw count types heads labels tupleBound)) := by
  have hi := OriginalUniverseDecoderTransportLeafAcceptanceProof.bottomIff H (OriginalUniverseDomainCoverage.member n)
    (OriginalGuardedHeadSourceCoverage.window n arity) raw payload typ gamma context hc
  have hp := Derivation.implicationElimination (Classical.choice (andLeft hi)) (Classical.choice ha)
  have hm := OriginalUniverseDomainCoverage.MemberProof.membership n typ context types
    ⟨Derivation.conjunctionLeft hp⟩ (MetadataProof.typesAt seed param context types hcontext htypes)
  have he : Nonempty (Derivation body Delta (eqn typ payload)) := by
    have h : Nonempty (Derivation body Delta (equal payload typ)) := ⟨Derivation.conjunctionRight hp⟩
    rw [InternalControlGraphSupportProof.equalEqn] at h
    exact ⟨symm (Classical.choice h)⟩
  have hmember : Nonempty (Derivation body Delta (graph2 contains (numeral 1) types payload)) := by
    unfold graph2 programGraph at hm ⊢
    apply InternalGraphCompositionEqualityProof.graphInputTransport body alpha 2 Delta
      (OrdinaryArithmetic.graphFormula contains) (numeral 1) ![types,typ] ![types,payload] _ hm
    intro i
    fin_cases i
    · rw [InternalSourceInversionSupportProof.onEquality]; exact ⟨refl types⟩
    · rw [InternalSourceInversionSupportProof.onEquality]; exact he
  exact (OriginalEnumerationFields.LeafProof.internalBottom n body alpha Delta raw count types heads labels tupleBound payload hc).mpr
    (andIntro (OriginalEnumerationValidity.LeafProof.bottom n raw payload hc) hmember)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.BottomProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.BottomProof
