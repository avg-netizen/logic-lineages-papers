module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.UnaryMeaningProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldLeafConstructorsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.MeaningSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.ListBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.ReverseLambdaProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.ReverseBinaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserUnaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserBinaryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.ReverseTaggedProof
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

theorem lambdaCase (n : Nat) (bound fuel types heads labels tupleBound prior raw : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 rawTag (numeral 1) raw)))
    (hi : Nonempty (Derivation body Delta (Lists.Characterizes n prior (suc bound) fuel types heads labels tupleBound)))
    (h : Nonempty (Derivation body Delta (Meaning.holds n raw bound (suc fuel) types heads labels tupleBound))) :
    Nonempty (Derivation body Delta (OriginalEnumerationLayerFields.Targets.lambdaCase types prior raw)) := by
  apply OriginalRawSyntaxTransportInternalParserUnaryProof.lambdaCases raw _ ht
  intro beta j Theta typ child hj hc
  rw [OriginalEnumerationLayerFields.LambdaSyntaxProof.caseRename]
  have hij := renameInto hi j Theta hj
  simp only [ListSyntaxProof.allRename,InternalTagArithmeticSyntaxProof.sucRelabel] at hij
  have hmj := renameInto h j Theta hj
  simp only [meaningRename,InternalTagArithmeticSyntaxProof.sucRelabel] at hmj
  exact ReverseLambdaProof.atConstructor n (bound.relabel j) (fuel.relabel j) (types.relabel j) (heads.relabel j)
    (labels.relabel j) (tupleBound.relabel j) (prior.relabel j) (raw.relabel j) typ child hij hc hmj

theorem application (n : Nat) (bound fuel types heads labels tupleBound prior raw : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 rawTag (numeral 2) raw)))
    (hi : Nonempty (Derivation body Delta (Lists.Characterizes n prior bound fuel types heads labels tupleBound)))
    (h : Nonempty (Derivation body Delta (Meaning.holds n raw bound (suc fuel) types heads labels tupleBound))) :
    Nonempty (Derivation body Delta (OriginalEnumerationLayerFields.Targets.typedBinaryCase applicationConstructor types prior raw)) := by
  apply OriginalRawSyntaxTransportInternalParserBinaryProof.applicationCases raw _ ht
  intro beta j Theta typ left right hj hc
  rw [OriginalEnumerationLayerFields.BinarySyntaxProof.caseRename]
  have hij := renameInto hi j Theta hj
  simp only [ListSyntaxProof.allRename,InternalTagArithmeticSyntaxProof.sucRelabel] at hij
  have hmj := renameInto h j Theta hj
  simp only [meaningRename,InternalTagArithmeticSyntaxProof.sucRelabel] at hmj
  exact ReverseBinaryProof.application n (bound.relabel j) (fuel.relabel j) (types.relabel j) (heads.relabel j)
    (labels.relabel j) (tupleBound.relabel j) (prior.relabel j) (raw.relabel j) typ left right hij hc hmj

theorem cons (n : Nat) (bound fuel types heads labels tupleBound prior raw : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 rawTag (numeral 7) raw)))
    (hi : Nonempty (Derivation body Delta (Lists.Characterizes n prior bound fuel types heads labels tupleBound)))
    (h : Nonempty (Derivation body Delta (Meaning.holds n raw bound (suc fuel) types heads labels tupleBound))) :
    Nonempty (Derivation body Delta (OriginalEnumerationLayerFields.Targets.typedBinaryCase consConstructor types prior raw)) := by
  apply OriginalRawSyntaxTransportInternalParserBinaryProof.consCases raw _ ht
  intro beta j Theta typ left right hj hc
  rw [OriginalEnumerationLayerFields.BinarySyntaxProof.caseRename]
  have hij := renameInto hi j Theta hj
  simp only [ListSyntaxProof.allRename,InternalTagArithmeticSyntaxProof.sucRelabel] at hij
  have hmj := renameInto h j Theta hj
  simp only [meaningRename,InternalTagArithmeticSyntaxProof.sucRelabel] at hmj
  exact ReverseBinaryProof.cons n (bound.relabel j) (fuel.relabel j) (types.relabel j) (heads.relabel j)
    (labels.relabel j) (tupleBound.relabel j) (prior.relabel j) (raw.relabel j) typ left right hij hc hmj

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.ReverseTaggedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.ReverseTaggedProof
