module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.ParameterTransportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.SelectorInputProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.LayerGuardProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.HeadAllowedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.HeadInputProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open OriginalRawSyntaxTransportInternalConstructorSupportProof
open InputProof ParameterTransportProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem headsAt (xs : Fin 6 → OTerm alpha) (key answers param : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph parameterQuery param xs))) :
    Nonempty (Derivation body Delta (graph3 heads (xs 3) key answers param)) := by
  apply programCases middleQuery xs _
  intro beta j Theta middle hj hm
  rw [graph3Rename]
  have hpj := renameInto hp j Theta hj
  rw [programRename] at hpj
  have hleft := pairOfLeft (.projection 3) innerQuery middle ((xs 3).relabel j)
    (fun i => (xs i).relabel j) hm (projectionValue 3 (fun i : Fin 6 => (xs i).relabel j))
  have hright := pairOfRight (.projection 2) middleQuery (param.relabel j) middle
    (fun i => (xs i).relabel j) hpj hm
  have hmiddle := unaryValue InternalUnpair.right (.projection 2) middle (param.relabel j)
    ![key.relabel j,answers.relabel j,param.relabel j] hright
    (projectionValue 2 ![key.relabel j,answers.relabel j,param.relabel j])
  exact unaryValue InternalUnpair.left (rightOf (.projection 2)) ((xs 3).relabel j) middle
    ![key.relabel j,answers.relabel j,param.relabel j] hleft hmiddle
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.HeadInputProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.HeadInputProof
