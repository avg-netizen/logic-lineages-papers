module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.UnaryMeaningProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldLeafConstructorsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.MeaningSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.ListBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.GuardObservationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.ReverseObservedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.LayerReverseProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalVariableSupportProof
open OriginalRawSyntaxTransportInternalConstructorFieldsProof OriginalRawSyntaxTransportInternalConstructorSelectorsProof
open InternalQuotientComparisonProof (orLeft orRight)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261115
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open MeaningSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open TwoSol20261113.CalibratedPrimary.Membership (contains)

theorem alternatives (n : Nat) (xs : Fin 7 → OTerm alpha) (fuel raw : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (Lists.Characterizes n (xs 5) (xs 4) fuel (xs 0) (xs 1) (xs 2) (xs 3))))
    (ho : Nonempty (Derivation body Delta (Lists.Characterizes n (xs 6) (suc (xs 4)) fuel (xs 0) (xs 1) (xs 2) (xs 3))))
    (h : Nonempty (Derivation body Delta (Meaning.holds n raw (xs 4) (suc fuel) (xs 0) (xs 1) (xs 2) (xs 3)))) :
    Nonempty (Derivation body Delta (OriginalEnumerationLayerFields.Targets.alternatives n xs raw)) := by
  have hv := OriginalEnumerationFields.AcceptanceProof.validFromFields n ![raw,xs 4,xs 0,xs 1,xs 2,xs 3] (andLeft h)
  apply GuardObservationProof.cases n raw _ hv
  intro beta j Theta tag payload first second head hj hp hf hs hh ha
  rw [OriginalEnumerationLayerFields.AssemblyProof.alternativesRename]
  have hij := renameInto hi j Theta hj
  rw [ListSyntaxProof.allRename] at hij
  have hoj := renameInto ho j Theta hj
  simp only [ListSyntaxProof.allRename,InternalTagArithmeticSyntaxProof.sucRelabel] at hoj
  have hmj := renameInto h j Theta hj
  simp only [meaningRename,InternalTagArithmeticSyntaxProof.sucRelabel] at hmj
  exact ReverseObservedProof.atFields n (fun i => (xs i).relabel j) (fuel.relabel j) (raw.relabel j)
    tag payload first second head hp ha hij hoj hmj
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.LayerReverseProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.LayerReverseProof
