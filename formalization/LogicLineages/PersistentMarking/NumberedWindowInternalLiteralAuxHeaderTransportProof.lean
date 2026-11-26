module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxRootLeafDefinitions
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxHeaderTransportProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue programRename)
open ID1Completion.InternalAcceptanceSupportProof (programCases compositionRecover)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (inputsRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparseRawFunctionFrame (frameSlot)
open NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof (onTape)
open NumberedWindowInternalLiteralAuxRootLeaf (functionLambdaHeader lambdaHeader)

abbrev D (B : Positive (Fin 1)) {α : Type} (Γ : List (Formula α)) (f : Formula α) :=
  Nonempty (Derivation B Γ f)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- The actual function-header graph depends only on the original
source field. Replacing the surrounding root payload or target
does not replace the selected raw function. -/
theorem exact_OpenFunctionHeaderTransport (q w r w' r' out : OTerm α)
    (held : D B Γ (programGraph functionLambdaHeader out ![q,w,r])) :
    D B Γ (programGraph functionLambdaHeader out ![q,w',r']) := by
  apply programCases (field 2) ![q] _
  intro β j Δ x keep value
  rw [programRename,tripleInputsRename]
  rw [inputsRename] at value
  have g := renameInto held j Δ keep
  rw [programRename,tripleInputsRename] at g
  let left : Fin 3 → OTerm β := ![q.relabel j,w.relabel j,r.relabel j]
  let right : Fin 3 → OTerm β := ![q.relabel j,w'.relabel j,r'.relabel j]
  have cod : D B Δ (unary lambdaHeader (out.relabel j) x) := by
    apply compositionRecover lambdaHeader ![frameSlot 2 0] (out.relabel j) left ![x] g
    intro i
    obtain rfl := Fin.eq_zero i
    exact onTape (field 2) 0 x left value
  apply compositionValue lambdaHeader ![frameSlot 2 0] (out.relabel j) right ![x] cod
  intro i
  obtain rfl := Fin.eq_zero i
  exact onTape (field 2) 0 x right value

#print axioms exact_OpenFunctionHeaderTransport
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxHeaderTransportProof
