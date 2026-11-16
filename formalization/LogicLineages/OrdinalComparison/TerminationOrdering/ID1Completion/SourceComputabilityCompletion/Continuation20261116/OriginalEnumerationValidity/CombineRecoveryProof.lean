module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.NodeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldLeafConstructorsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.CombineRecoveryProof
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

open OriginalEnumerationRecursionInterface
open InternalAcceptanceSupportProof
theorem positive (n : Nat) (node answers param fuel out : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (graph3 OriginalEnumerationRecursionInterface.fuel (suc fuel) node answers param)))
    (hg : Nonempty (Derivation body Delta (graph3 (G n) (suc out) node answers param))) :
    Nonempty (Derivation body Delta (graph3 (positiveLayer n) out node answers param)) := by
  apply programCases (positiveLayer n) (Fin.cons node (Fin.cons answers (Fin.cons param Fin.elim0))) _
  intro beta j Theta value hj hv
  simp only [graph3Rename]
  simp only [InternalRecursionGraphStepSyntaxProof.consTermRename,InternalControlGraphSupportProof.emptyRename] at hv
  have hfj := renameInto hf j Theta hj
  have hgj := renameInto hg j Theta hj
  simp only [graph3Rename,InternalTagArithmeticSyntaxProof.sucRelabel] at hfj hgj
  have hx := CombineScalarProof.positiveValue n (node.relabel j) (answers.relabel j) (param.relabel j) (fuel.relabel j) value hfj hv
  obtain ⟨he⟩ := valueUnique (G n) (suc value) (suc (out.relabel j)) ![node.relabel j,answers.relabel j,param.relabel j] hx hgj
  exact outputTransport (positiveLayer n) value (out.relabel j) ![node.relabel j,answers.relabel j,param.relabel j]
    ⟨cancelSuc he⟩ hv

theorem zero (n : Nat) (node answers param out : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (graph3 OriginalEnumerationRecursionInterface.fuel z node answers param)))
    (hg : Nonempty (Derivation body Delta (graph3 (G n) (suc out) node answers param))) :
    Nonempty (Derivation body Delta (eqn out z)) := by
  obtain ⟨he⟩ := valueUnique (G n) (suc out) (suc z) ![node,answers,param] hg
    (CombineScalarProof.zeroValue n node answers param hf)
  exact ⟨cancelSuc he⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.CombineRecoveryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.CombineRecoveryProof
