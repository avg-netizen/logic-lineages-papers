module
public import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepTargets
import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepRootProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepContextProof
public section

namespace LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepChecks
open NumberedWindowAtomicRawStep NumberedWindowAtomicRawStepTargets
open NumberedWindowAtomicRawStepFieldProof (atomicFields)
open NumberedWindowAtomicRawStepRootProof (atomicRoots)
open NumberedWindowAtomicRawStepContextProof (noContext runRoot)
open NumberedWindowRawContextAlgorithm (next raw run windowStep)
open NumberedWindowConcreteCheckers (root step)
open NumberedWindowScalarAlgorithm (Settings admitted)
open NumberedWindowCopyAlgorithm (Entries)

/-- Retain both the original root witness existence and the literal
window admission condition of this same actual accepted target. -/
private theorem acceptedCallback (xs : Entries) (s : Settings) (Γ : List Nat) (requested q w y : Nat)
    (no : ∀ tag ws, next tag ws q y = none)
    (h : step xs s Γ requested q w y = true) :
    (∃ v, root xs s q v y = true) ∧ admitted s Γ requested y = true := by
  simp only [step,windowStep,raw,Bool.and_eq_true,and_assoc] at h
  exact ⟨runRoot (root xs s) w q w y no h.2.2.1,h.2.2.2.2⟩

theorem exact_AtomicRawFields : ExactAtomicRawFields := atomicFields

theorem exact_ConcreteAtomicRoot : ExactConcreteAtomicRoot := atomicRoots

theorem exact_AtomicNoContextDescent : ExactAtomicNoContextDescent := noContext

theorem exact_ConcreteAtomicRawStep : ExactConcreteAtomicRawStep := by
  constructor
  · intro xs s Γ requested t n w y h
    obtain ⟨⟨v,supplied⟩,target⟩ := acceptedCallback xs s Γ requested (freeRaw t n) w y
      (fun tag ws => noContext.1 tag ws t n y) h
    have shape := (atomicRoots.1 xs s t n v y supplied).1
    rw [shape] at target
    exact ⟨shape,target⟩
  · intro xs s Γ requested t w y
    cases h : step xs s Γ requested (bottomRaw t) w y with
    | false => rfl
    | true =>
      obtain ⟨⟨v,supplied⟩,_⟩ := acceptedCallback xs s Γ requested (bottomRaw t) w y
        (fun tag ws => noContext.2 tag ws t y) h
      rw [atomicRoots.2 xs s t v y] at supplied
      cases supplied

#print axioms exact_AtomicRawFields
#print axioms exact_ConcreteAtomicRoot
#print axioms exact_AtomicNoContextDescent
#print axioms exact_ConcreteAtomicRawStep
end LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepChecks
