module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.LeafMeaningProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldLeafConstructorsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.MeaningSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.LayerLeafProof
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

theorem variableCase (n : Nat) (bound fuel types heads labels tupleBound raw : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) raw)))
    (h : Nonempty (Derivation body Delta (OriginalEnumerationLayerFields.Targets.variableCase bound raw))) :
    Nonempty (Derivation body Delta (Meaning.holds n raw bound (suc fuel) types heads labels tupleBound)) := by
  apply OriginalEnumerationLayerFields.VariableSyntaxProof.cases bound raw _ h
  intro beta j Theta ys hj hf
  simp only [meaningRename,InternalTagArithmeticSyntaxProof.sucRelabel]
  have hvj := renameInto hv j Theta hj
  simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename] at hvj
  exact (LeafMeaningProof.variableCode n (raw.relabel j) (bound.relabel j) (fuel.relabel j) (types.relabel j)
    (heads.relabel j) (labels.relabel j) (tupleBound.relabel j) (ys 0) (andRight hf)).mpr
    (andIntro hvj (andLeft hf))

theorem bottomCase (n : Nat) (bound fuel types heads labels tupleBound raw : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) raw)))
    (h : Nonempty (Derivation body Delta (OriginalEnumerationLayerFields.Targets.bottomCase types raw))) :
    Nonempty (Derivation body Delta (Meaning.holds n raw bound (suc fuel) types heads labels tupleBound)) := by
  apply OriginalEnumerationLayerFields.BottomSyntaxProof.cases types raw _ h
  intro beta j Theta ys hj hf
  simp only [meaningRename,InternalTagArithmeticSyntaxProof.sucRelabel]
  have hvj := renameInto hv j Theta hj
  simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename] at hvj
  exact (LeafMeaningProof.bottom n (raw.relabel j) (bound.relabel j) (fuel.relabel j) (types.relabel j)
    (heads.relabel j) (labels.relabel j) (tupleBound.relabel j) (ys 0) (andRight hf)).mpr
    (andIntro hvj (andLeft hf))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.LayerLeafProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.LayerLeafProof
