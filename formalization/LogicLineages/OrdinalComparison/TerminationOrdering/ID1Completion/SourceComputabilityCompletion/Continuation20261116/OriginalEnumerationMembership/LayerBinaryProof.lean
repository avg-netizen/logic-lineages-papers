module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.BinaryMeaningProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldLeafConstructorsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.MeaningSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.ListBindingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.LayerBinaryProof
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

theorem application (n : Nat) (bound fuel types heads labels tupleBound prior raw : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) raw)))
    (hi : Nonempty (Derivation body Delta (Lists.Characterizes n prior bound fuel types heads labels tupleBound)))
    (h : Nonempty (Derivation body Delta (OriginalEnumerationLayerFields.Targets.typedBinaryCase applicationConstructor types prior raw))) :
    Nonempty (Derivation body Delta (Meaning.holds n raw bound (suc fuel) types heads labels tupleBound)) := by
  apply OriginalEnumerationLayerFields.BinarySyntaxProof.cases applicationConstructor types prior raw _ h
  intro beta j Theta ys hj hf
  simp only [meaningRename,InternalTagArithmeticSyntaxProof.sucRelabel]
  have hvj := renameInto hv j Theta hj
  simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename] at hvj
  have hij := renameInto hi j Theta hj
  rw [ListSyntaxProof.allRename] at hij
  have hl := (ListBindingProof.atRaw n (prior.relabel j) (bound.relabel j) (fuel.relabel j)
    (types.relabel j) (heads.relabel j) (labels.relabel j) (tupleBound.relabel j) (ys 1) hij).mp
    (andRight (andLeft (andLeft hf)))
  have hr := (ListBindingProof.atRaw n (prior.relabel j) (bound.relabel j) (fuel.relabel j)
    (types.relabel j) (heads.relabel j) (labels.relabel j) (tupleBound.relabel j) (ys 2) hij).mp
    (andRight (andLeft hf))
  exact (BinaryMeaningProof.application n (raw.relabel j) (bound.relabel j) (fuel.relabel j) (types.relabel j)
    (heads.relabel j) (labels.relabel j) (tupleBound.relabel j) (ys 0) (ys 1) (ys 2) (andRight hf)).mpr
    (andIntro hvj (andIntro (andIntro (andLeft (andLeft (andLeft hf))) hl) hr))

theorem cons (n : Nat) (bound fuel types heads labels tupleBound prior raw : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) raw)))
    (hi : Nonempty (Derivation body Delta (Lists.Characterizes n prior bound fuel types heads labels tupleBound)))
    (h : Nonempty (Derivation body Delta (OriginalEnumerationLayerFields.Targets.typedBinaryCase consConstructor types prior raw))) :
    Nonempty (Derivation body Delta (Meaning.holds n raw bound (suc fuel) types heads labels tupleBound)) := by
  apply OriginalEnumerationLayerFields.BinarySyntaxProof.cases consConstructor types prior raw _ h
  intro beta j Theta ys hj hf
  simp only [meaningRename,InternalTagArithmeticSyntaxProof.sucRelabel]
  have hvj := renameInto hv j Theta hj
  simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename] at hvj
  have hij := renameInto hi j Theta hj
  rw [ListSyntaxProof.allRename] at hij
  have hl := (ListBindingProof.atRaw n (prior.relabel j) (bound.relabel j) (fuel.relabel j)
    (types.relabel j) (heads.relabel j) (labels.relabel j) (tupleBound.relabel j) (ys 1) hij).mp
    (andRight (andLeft (andLeft hf)))
  have hr := (ListBindingProof.atRaw n (prior.relabel j) (bound.relabel j) (fuel.relabel j)
    (types.relabel j) (heads.relabel j) (labels.relabel j) (tupleBound.relabel j) (ys 2) hij).mp
    (andRight (andLeft hf))
  exact (BinaryMeaningProof.cons n (raw.relabel j) (bound.relabel j) (fuel.relabel j) (types.relabel j)
    (heads.relabel j) (labels.relabel j) (tupleBound.relabel j) (ys 0) (ys 1) (ys 2) (andRight hf)).mpr
    (andIntro hvj (andIntro (andIntro (andLeft (andLeft (andLeft hf))) hl) hr))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.LayerBinaryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.LayerBinaryProof
