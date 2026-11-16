module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.UnaryMeaningProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldLeafConstructorsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.MeaningSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.ListBindingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.LayerOrdinaryProof
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

theorem forward (n : Nat) (bound fuel types heads labels tupleBound prior raw : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) raw)))
    (hi : Nonempty (Derivation body Delta (Lists.Characterizes n prior bound fuel types heads labels tupleBound)))
    (h : Nonempty (Derivation body Delta (OriginalEnumerationLayerFields.Targets.ordinaryCase n heads prior raw))) :
    Nonempty (Derivation body Delta (Meaning.holds n raw bound (suc fuel) types heads labels tupleBound)) := by
  apply OriginalEnumerationLayerFields.OrdinarySyntaxProof.cases n heads prior raw _ h
  intro beta j Theta ys hj hf
  simp only [meaningRename,InternalTagArithmeticSyntaxProof.sucRelabel]
  have hvj := renameInto hv j Theta hj
  simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename] at hvj
  have hij := renameInto hi j Theta hj
  rw [ListSyntaxProof.allRename] at hij
  have hm := (ListBindingProof.atRaw n (prior.relabel j) (bound.relabel j) (fuel.relabel j)
    (types.relabel j) (heads.relabel j) (labels.relabel j) (tupleBound.relabel j) (ys 2) hij).mp
    (andRight (andLeft hf))
  have hh := OriginalEncodedNumberedEnumerationBranch.MapImageProof.introduce (OriginalEncodedHeadConversion.convert n)
    (heads.relabel j) (ys 1) (ys 0) (andLeft (andLeft (andLeft hf))) (andRight (andLeft (andLeft hf)))
  exact (UnaryMeaningProof.ordinaryCase n (raw.relabel j) (bound.relabel j) (fuel.relabel j) (types.relabel j)
    (heads.relabel j) (labels.relabel j) (tupleBound.relabel j) (ys 1) (ys 2) (andRight hf)).mpr
    (andIntro hvj (andIntro hh hm))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.LayerOrdinaryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.LayerOrdinaryProof
