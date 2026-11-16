module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.UnaryMeaningProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldLeafConstructorsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.MeaningSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.ListBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.ReverseLambdaProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.ReverseBinaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserUnaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserBinaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.ReverseOrdinaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.ReverseNumberedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserNumberedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.ReverseHeadTaggedProof
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

theorem ordinary (n : Nat) (bound fuel types heads labels tupleBound prior raw : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 rawTag (numeral 4) raw)))
    (hi : Nonempty (Derivation body Delta (Lists.Characterizes n prior bound fuel types heads labels tupleBound)))
    (h : Nonempty (Derivation body Delta (Meaning.holds n raw bound (suc fuel) types heads labels tupleBound))) :
    Nonempty (Derivation body Delta (OriginalEnumerationLayerFields.Targets.ordinaryCase n heads prior raw)) := by
  apply OriginalRawSyntaxTransportInternalParserUnaryProof.ordinaryCases raw _ ht
  intro beta j Theta head child hj hc
  rw [OriginalEnumerationLayerFields.OrdinarySyntaxProof.caseRename]
  have hij := renameInto hi j Theta hj
  rw [ListSyntaxProof.allRename] at hij
  have hmj := renameInto h j Theta hj
  simp only [meaningRename,InternalTagArithmeticSyntaxProof.sucRelabel] at hmj
  exact ReverseOrdinaryProof.atConstructor n (bound.relabel j) (fuel.relabel j) (types.relabel j) (heads.relabel j)
    (labels.relabel j) (tupleBound.relabel j) (prior.relabel j) (raw.relabel j) head child hij hc hmj

theorem numbered (n : Nat) (bound fuel types heads labels tupleBound prior raw : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 rawTag (numeral 5) raw)))
    (hi : Nonempty (Derivation body Delta (Lists.Characterizes n prior bound fuel types heads labels tupleBound)))
    (h : Nonempty (Derivation body Delta (Meaning.holds n raw bound (suc fuel) types heads labels tupleBound))) :
    Nonempty (Derivation body Delta (OriginalEnumerationLayerFields.Targets.numberedCase n labels heads types tupleBound prior raw)) := by
  apply OriginalRawSyntaxTransportInternalParserNumberedProof.numberedCases raw _ ht
  intro beta j Theta label head typ base typeList extra hj hc
  rw [OriginalEnumerationLayerFields.NumberedSyntaxProof.caseRename]
  have hij := renameInto hi j Theta hj
  rw [ListSyntaxProof.allRename] at hij
  have hmj := renameInto h j Theta hj
  simp only [meaningRename,InternalTagArithmeticSyntaxProof.sucRelabel] at hmj
  exact ReverseNumberedProof.atConstructor n (bound.relabel j) (fuel.relabel j) (types.relabel j) (heads.relabel j)
    (labels.relabel j) (tupleBound.relabel j) (prior.relabel j) (raw.relabel j) label head typ base typeList extra hij hc hmj

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.ReverseHeadTaggedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.ReverseHeadTaggedProof
