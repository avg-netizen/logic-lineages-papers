module

public import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneVariableFrontSyntaxTargetsV2
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafIntrinsicShapeProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof

/-! Proof of the frozen `OpenVariableFrontSyntax`
(`Paper16AccessibilityMilestoneVariableFrontSyntaxTargetsV2`; Fable B2, 27 November 2026).
The header and field reports at a named leaf are the accepted
`exact_OpenCoverNamedLeafIntrinsicShape`; the branch is entered by `successorBranchIntro`. -/

public section

namespace LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneVariableFrontSyntaxOpenProofV2

open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (branch)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchIntro)
open ID1Completion.InternalControlGraphSupportProof (compositionValue)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalCoverNamedLeavesTargets (namedTerm)
open NumberedWindowInternalCoverNamedLeafIntrinsicShapeProof (exact_OpenCoverNamedLeafIntrinsicShape)
open NumberedWindowInternalCoverSelectedValidityTargets (header)
open NumberedWindowInternalSparsePathEnvelope (field applyUnary)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open Paper16AccessibilityMilestoneVariableFrontSyntaxTargetsV2

attribute [local irreducible] programGraph

theorem exact_OpenVariableFrontSyntax : OpenVariableFrontSyntax := by
  intro TV V body α Γ ty i out typed
  obtain ⟨_, _, headerYes, typeField, _, _⟩ :=
    exact_OpenCoverNamedLeafIntrinsicShape false body α Γ ty i
  have headerYes' : Nonempty (Derivation body Γ
      (programGraph (header 0 2) (suc z) ![namedTerm 0 ty i])) := headerYes
  have typeField' : Nonempty (Derivation body Γ
      (programGraph (field 0) ty ![namedTerm 0 ty i])) := typeField
  have typed' : Nonempty (Derivation body Γ (programGraph TV out ![ty])) := typed
  change Nonempty (Derivation body Γ
    (programGraph (branch (header 0 2) V (.composition TV (fun _ : Fin 1 => field 0))) out
      ![namedTerm 0 ty i]))
  apply successorBranchIntro (header 0 2) V (.composition TV (fun _ : Fin 1 => field 0)) out z
    ![namedTerm 0 ty i] headerYes'
  apply compositionValue TV (fun _ : Fin 1 => field 0) out ![namedTerm 0 ty i] ![ty] typed'
  intro k
  obtain rfl := Fin.eq_zero k
  exact typeField'

#print axioms exact_OpenVariableFrontSyntax

end LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneVariableFrontSyntaxOpenProofV2
