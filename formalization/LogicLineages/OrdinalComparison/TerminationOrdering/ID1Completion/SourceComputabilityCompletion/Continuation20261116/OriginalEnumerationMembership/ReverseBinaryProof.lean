module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.BinaryMeaningProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldLeafConstructorsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.MeaningSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.ListBindingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.ReverseBinaryProof
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

theorem application (n : Nat) (bound fuel types heads labels tupleBound prior raw typ left right : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (Lists.Characterizes n prior bound fuel types heads labels tupleBound)))
    (hc : Nonempty (Derivation body Delta (graph3 applicationConstructor raw typ left right)))
    (h : Nonempty (Derivation body Delta (Meaning.holds n raw bound (suc fuel) types heads labels tupleBound))) :
    Nonempty (Derivation body Delta (OriginalEnumerationLayerFields.Targets.typedBinaryCase applicationConstructor types prior raw)) := by
  have hf := (BinaryMeaningProof.application n raw bound fuel types heads labels tupleBound typ left right hc).mp h
  have hl := (ListBindingProof.atRaw n prior bound fuel types heads labels tupleBound left hi).mpr
    (andRight (andLeft (andRight hf)))
  have hr := (ListBindingProof.atRaw n prior bound fuel types heads labels tupleBound right hi).mpr
    (andRight (andRight hf))
  exact OriginalEnumerationLayerFields.BinarySyntaxProof.introduce applicationConstructor types prior raw ![typ,left,right]
    (andIntro (andIntro (andIntro (andLeft (andLeft (andRight hf))) hl) hr) hc)

theorem cons (n : Nat) (bound fuel types heads labels tupleBound prior raw typ left right : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (Lists.Characterizes n prior bound fuel types heads labels tupleBound)))
    (hc : Nonempty (Derivation body Delta (graph3 consConstructor raw typ left right)))
    (h : Nonempty (Derivation body Delta (Meaning.holds n raw bound (suc fuel) types heads labels tupleBound))) :
    Nonempty (Derivation body Delta (OriginalEnumerationLayerFields.Targets.typedBinaryCase consConstructor types prior raw)) := by
  have hf := (BinaryMeaningProof.cons n raw bound fuel types heads labels tupleBound typ left right hc).mp h
  have hl := (ListBindingProof.atRaw n prior bound fuel types heads labels tupleBound left hi).mpr
    (andRight (andLeft (andRight hf)))
  have hr := (ListBindingProof.atRaw n prior bound fuel types heads labels tupleBound right hi).mpr
    (andRight (andRight hf))
  exact OriginalEnumerationLayerFields.BinarySyntaxProof.introduce consConstructor types prior raw ![typ,left,right]
    (andIntro (andIntro (andIntro (andLeft (andLeft (andRight hf))) hl) hr) hc)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.ReverseBinaryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.ReverseBinaryProof
