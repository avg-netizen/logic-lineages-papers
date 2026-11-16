module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.ZeroDepthProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.MeaningDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.ZeroProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.ZeroProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open Continuation20261115
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem atKnown (n : Nat) (node param out raw bound types heads labels tupleBound : OTerm alpha)
    (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node bound z)))
    (he : Nonempty (Derivation body Delta (graph2 (OriginalEnumerationRecursion.enumeration n) out node param))) :
    (Nonempty (Derivation body Delta (graph2 contains (numeral 1) out raw)) ↔
     Nonempty (Derivation body Delta (Meaning.holds n raw bound z types heads labels tupleBound))) := by
  constructor
  · intro hm
    have hz := OriginalEnumerationValidity.ZeroProof.outputZero n node param bound out hn he
    have hm0 := InternalControlGraphSupportProof.headTransport contains (numeral 1) out z (Fin.cons raw Fin.elim0) hz hm
    exact ⟨Derivation.explosion (Classical.choice (OriginalAscendingRange.SupportProof.nilImpossible raw hm0))⟩
  · intro hm
    exact ⟨Derivation.explosion (Classical.choice (ZeroDepthProof.fieldsZeroImpossible n raw bound types heads labels tupleBound (andLeft hm) (andRight hm)))⟩

theorem atKnownFormula (n : Nat) (node param out raw bound types heads labels tupleBound : OTerm alpha)
    (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node bound z)))
    (he : Nonempty (Derivation body Delta (graph2 (OriginalEnumerationRecursion.enumeration n) out node param))) :
    Nonempty (Derivation body Delta
      ((graph2 contains (numeral 1) out raw).imp (Meaning.holds n raw bound z types heads labels tupleBound) ⊓
       (Meaning.holds n raw bound z types heads labels tupleBound).imp (graph2 contains (numeral 1) out raw))) := by
  apply andIntro
  · apply Nonempty.intro
    apply Derivation.implicationIntroduction
    exact Classical.choice ((atKnown n node param out raw bound types heads labels tupleBound
      (withHyp hn _) (withHyp he _)).mp ⟨Derivation.hypothesis List.mem_cons_self⟩)
  · apply Nonempty.intro
    apply Derivation.implicationIntroduction
    exact Classical.choice ((atKnown n node param out raw bound types heads labels tupleBound
      (withHyp hn _) (withHyp he _)).mpr ⟨Derivation.hypothesis List.mem_cons_self⟩)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.ZeroProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.ZeroProof
