module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicShapeDecodeProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicDirectRulesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralFactsSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityDownwardSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicNeutralStepProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.SourcePresentation (sourceBody)
open ID1Completion.InternalControlGraphSupportProof (equalEqn)
open ID1Completion.InternalComputabilityDownwardSyntaxProof (edgeRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalLiteralHopCarrier (rawWithTarget)
open NumberedWindowInternalLiteralAddressedChildReportsProof (S hop)
open NumberedWindowInternalNeutralFactsTargets (atom direct)
open NumberedWindowInternalNeutralFactsSyntaxProof (atomRename)
open NumberedWindowInternalAtomicRefinement (freeSource bottomSource)
open NumberedWindowInternalAtomicRefinementObjectTargets (packedBottomTerm)
open NumberedWindowInternalAtomicRefinementObjectChecks (exact_OpenAtomicRecognition)
open NumberedWindowInternalLiteralAtomicRawGuardProof (guardedRaw)
open NumberedWindowInternalLiteralAtomicLeastGuardProof (guardedLeast)
open NumberedWindowInternalLiteralAtomicLeastOpenProof (D)
open NumberedWindowInternalLiteralAtomicShapeDecodeProof (exact_OpenLiteralAtomicShapeDecode)
open NumberedWindowInternalLiteralAtomicDirectRulesProof
  (exact_OpenLiteralAtomicBottomNoDirect exact_OpenLiteralAtomicFreeDirectBottom)

variable {α : Type} {Γ : List (Formula α)}

/-- The bottom-no-step field of the neutral arithmetic, with the true
open bottom selector as its only source-shape premise. -/
theorem exact_OpenLiteralAtomicBottomNoStep (i cv tv : Program 1) (raw : Program 5)
    (L : Program 3) (c : Nat) (x y : OTerm α) :
    let L' := guardedLeast L
    let R := rawWithTarget i cv tv (guardedRaw raw) L'
    let data := S i cv tv R L'
    let B := sourceBody data c
    D B Γ (atom bottomSource x) → D B Γ (direct data (hop cv tv R L') c x y) → D B Γ ⊥ := by
  intro L' R data B shape edge
  apply exact_OpenLiteralAtomicShapeDecode 3 0 x ⊥ shape
  intro β j Δ ctx t tail keep size literal
  rcases tail with _ | ⟨a,rest⟩ <;> simp at size
  have actual := renameInto edge j Δ keep
  simp only [direct,edgeRename] at actual
  exact exact_OpenLiteralAtomicBottomNoDirect i cv tv raw L c (x.relabel j) (y.relabel j)
    ctx t literal actual

/-- The variable-step field of the neutral arithmetic. An arbitrary
successful free selector is decoded; the true direct successor is
then recognized by the real bottom program in the same body. -/
theorem exact_OpenLiteralAtomicVariableStep (i cv tv : Program 1) (raw : Program 5)
    (L : Program 3) (c : Nat) (x y : OTerm α) :
    let L' := guardedLeast L
    let R := rawWithTarget i cv tv (guardedRaw raw) L'
    let data := S i cv tv R L'
    let B := sourceBody data c
    D B Γ (atom freeSource x) → D B Γ (direct data (hop cv tv R L') c x y) →
    D B Γ (atom bottomSource y) := by
  intro L' R data B shape edge
  apply exact_OpenLiteralAtomicShapeDecode 0 1 x (atom bottomSource y) shape
  intro β j Δ ctx t tail keep size literal
  rcases tail with _ | ⟨n,_ | ⟨a,rest⟩⟩ <;> simp at size
  rw [atomRename]
  have actual := renameInto edge j Δ keep
  simp only [direct,edgeRename] at actual
  have result := exact_OpenLiteralAtomicFreeDirectBottom i cv tv raw L c (x.relabel j)
    (y.relabel j) ctx t n literal actual
  have asShape : D B Δ (equal (y.relabel j) (packedBottomTerm ctx t)) := by
    rw [equalEqn]
    exact result
  obtain ⟨star⟩ := exact_OpenAtomicRecognition.2 B β Δ (y.relabel j) ctx t asShape
  exact ⟨Derivation.conjunctionRight star⟩

#print axioms exact_OpenLiteralAtomicBottomNoStep
#print axioms exact_OpenLiteralAtomicVariableStep
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicNeutralStepProof
