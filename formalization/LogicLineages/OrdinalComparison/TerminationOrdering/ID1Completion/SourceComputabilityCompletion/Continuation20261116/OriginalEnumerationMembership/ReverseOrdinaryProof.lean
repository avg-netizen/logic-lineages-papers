module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.UnaryMeaningProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldLeafConstructorsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.MeaningSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.ListBindingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.ReverseOrdinaryProof
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

theorem atConstructor (n : Nat) (bound fuel types heads labels tupleBound prior raw head child : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (Lists.Characterizes n prior bound fuel types heads labels tupleBound)))
    (hc : Nonempty (Derivation body Delta (graph2 ordinaryConstructor raw head child)))
    (h : Nonempty (Derivation body Delta (Meaning.holds n raw bound (suc fuel) types heads labels tupleBound))) :
    Nonempty (Derivation body Delta (OriginalEnumerationLayerFields.Targets.ordinaryCase n heads prior raw)) := by
  have hf := (UnaryMeaningProof.ordinaryCase n raw bound fuel types heads labels tupleBound head child hc).mp h
  have hm := (ListBindingProof.atRaw n prior bound fuel types heads labels tupleBound child hi).mpr
    (andRight (andRight hf))
  apply OriginalEncodedNumberedEnumerationBranch.MapImageEliminationProof.cases (OriginalEncodedHeadConversion.convert n)
    heads head _ (andLeft (andRight hf))
  intro beta j Theta encoded hj hmember hconvert
  rw [OriginalEnumerationLayerFields.OrdinarySyntaxProof.caseRename]
  have hcj := renameInto hc j Theta hj
  have hmj := renameInto hm j Theta hj
  rw [graph2Rename] at hcj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hmj
  exact OriginalEnumerationLayerFields.OrdinarySyntaxProof.introduce n (heads.relabel j) (prior.relabel j) (raw.relabel j)
    ![encoded,head.relabel j,child.relabel j]
    (andIntro (andIntro (andIntro hmember hconvert) hmj) hcj)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.ReverseOrdinaryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.ReverseOrdinaryProof
