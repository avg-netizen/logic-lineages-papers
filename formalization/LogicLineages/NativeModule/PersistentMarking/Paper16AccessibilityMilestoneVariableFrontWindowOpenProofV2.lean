module

public import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneVariableFrontWindowTargetsV2
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafIntrinsicShapeProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof

/-! Proof of the frozen `OpenVariableFrontWindow`
(`Paper16AccessibilityMilestoneVariableFrontWindowTargetsV2`; Fable B2, 27 November 2026). The
header and field reports at a named leaf are the accepted
`exact_OpenCoverNamedLeafIntrinsicShape`; the three branches are entered by
`successorBranchIntro`. -/

public section

namespace LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneVariableFrontWindowOpenProofV2

open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (branch constantZero)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchIntro)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue successorValue)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalCoverNamedLeavesTargets (namedTerm)
open NumberedWindowInternalCoverNamedLeafIntrinsicShapeProof (exact_OpenCoverNamedLeafIntrinsicShape)
open NumberedWindowInternalCoverSelectedValidityTargets (header)
open NumberedWindowInternalCoverTypeLeafIntrinsicTargets (onRaw)
open NumberedWindowInternalSparsePathEnvelope (field applyUnary)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open Paper16AccessibilityMilestoneVariableFrontWindowTargetsV2

attribute [local irreducible] programGraph

theorem exact_OpenVariableFrontWindow : OpenVariableFrontWindow := by
  intro T base body α Γ ctx ty i tag parsed typed
  let raw : OTerm α := namedTerm 0 ty i
  let xs : Fin 2 → OTerm α := ![ctx, raw]
  obtain ⟨_, _, headerYes, typeField, _, _⟩ :=
    exact_OpenCoverNamedLeafIntrinsicShape false body α Γ ty i
  have headerYes' : Nonempty (Derivation body Γ (programGraph (header 0 2) (suc z) ![raw])) :=
    headerYes
  have typeField' : Nonempty (Derivation body Γ (programGraph (field 0) ty ![raw])) := typeField
  have parsed' : Nonempty (Derivation body Γ (programGraph parser (suc tag) ![ctx])) := parsed
  have typed' : Nonempty (Derivation body Γ (programGraph T (suc z) ![ty])) := typed
  have atRaw (P : Program 1) (out : OTerm α)
      (h : Nonempty (Derivation body Γ (programGraph P out ![raw]))) :
      Nonempty (Derivation body Γ (programGraph
        (.composition P (fun _ : Fin 1 => (.projection 1 : Program 2))) out xs)) := by
    apply compositionValue P (fun _ : Fin 1 => (.projection 1 : Program 2)) out xs ![raw] h
    intro k
    obtain rfl := Fin.eq_zero k
    exact projectionValue (1 : Fin 2) xs
  have control : Nonempty (Derivation body Γ (programGraph (onRaw (header 0 2)) (suc z) xs)) :=
    atRaw (header 0 2) (suc z) headerYes'
  have context : Nonempty (Derivation body Γ (programGraph contextParsed (suc tag) xs)) := by
    apply compositionValue parser (fun _ : Fin 1 => (.projection 0 : Program 2)) (suc tag) xs
      ![ctx] parsed'
    intro k
    obtain rfl := Fin.eq_zero k
    exact projectionValue (0 : Fin 2) xs
  have guard : Nonempty (Derivation body Γ (programGraph (variableGuard T) (suc z) xs)) := by
    apply atRaw (.composition T (fun _ : Fin 1 => field 0)) (suc z)
    apply compositionValue T (fun _ : Fin 1 => field 0) (suc z) ![raw] ![ty] typed'
    intro k
    obtain rfl := Fin.eq_zero k
    exact typeField'
  have result : Nonempty (Derivation body Γ (programGraph variableResult (suc ty) xs)) := by
    apply atRaw (.composition .succ (fun _ : Fin 1 => field 0)) (suc ty)
    apply compositionValue .succ (fun _ : Fin 1 => field 0) (suc ty) ![raw] ![ty]
      (successorValue ![ty])
    intro k
    obtain rfl := Fin.eq_zero k
    exact typeField'
  change Nonempty (Derivation body Γ (programGraph
    (branch (onRaw (header 0 2)) base
      (branch contextParsed (constantZero 2)
        (branch (variableGuard T) (constantZero 2) variableResult))) (suc ty) xs))
  apply successorBranchIntro (onRaw (header 0 2)) base
    (branch contextParsed (constantZero 2)
      (branch (variableGuard T) (constantZero 2) variableResult)) (suc ty) z xs control
  apply successorBranchIntro contextParsed (constantZero 2)
    (branch (variableGuard T) (constantZero 2) variableResult) (suc ty) tag xs context
  exact successorBranchIntro (variableGuard T) (constantZero 2) variableResult (suc ty) z xs
    guard result

#print axioms exact_OpenVariableFrontWindow

end LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneVariableFrontWindowOpenProofV2
