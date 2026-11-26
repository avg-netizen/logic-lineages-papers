module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.LeafMeaningProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldLeafConstructorsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.MeaningSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.ReverseLeafProof
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

theorem variableCode (n : Nat) (bound fuel types heads labels tupleBound raw index : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph1 variableConstructor raw index)))
    (h : Nonempty (Derivation body Delta (Meaning.holds n raw bound (suc fuel) types heads labels tupleBound))) :
    Nonempty (Derivation body Delta (OriginalEnumerationLayerFields.Targets.variableCase bound raw)) := by
  have hf := (LeafMeaningProof.variableCode n raw bound fuel types heads labels tupleBound index hc).mp h
  exact OriginalEnumerationLayerFields.VariableSyntaxProof.introduce bound raw ![index]
    (andIntro (andRight hf) hc)

theorem bottom (n : Nat) (bound fuel types heads labels tupleBound raw typ : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph1 bottomConstructor raw typ)))
    (h : Nonempty (Derivation body Delta (Meaning.holds n raw bound (suc fuel) types heads labels tupleBound))) :
    Nonempty (Derivation body Delta (OriginalEnumerationLayerFields.Targets.bottomCase types raw)) := by
  have hf := (LeafMeaningProof.bottom n raw bound fuel types heads labels tupleBound typ hc).mp h
  exact OriginalEnumerationLayerFields.BottomSyntaxProof.introduce types raw ![typ]
    (andIntro (andRight hf) hc)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.ReverseLeafProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.ReverseLeafProof
