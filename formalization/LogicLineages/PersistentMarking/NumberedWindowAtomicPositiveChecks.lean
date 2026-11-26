module
public import LogicLineages.PersistentMarking.NumberedWindowAtomicPositiveTargets
import LogicLineages.PersistentMarking.NumberedWindowAtomicPositiveAddressSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicPositiveAdvanceProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicPositivePathProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedEmitterAddressProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowAtomicPositiveChecks
open NumberedWindowAtomicRawStep NumberedWindowAtomicPositiveTargets
open NumberedWindowAddressAlgorithm (addressView contextView typeBit)
open NumberedWindowConcreteCheckers (step positive)
open NumberedWindowScalarAlgorithm (Settings least scalar canonical)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowPositivePathAlgorithm (addressRS)
open NumberedWindowAtomicPositiveAddressSyntaxProof (literalView contextCode)
open NumberedWindowAtomicPositiveAdvanceProof (atomAdvance)
open NumberedWindowAtomicPositivePathProof (atomPositivePath)
open NumberedWindowInternalFreshProbeParsedEmitterAddressProof (addressCoordinates)

private theorem actualPath (xs : Entries) (s : Settings) {rawCtx t payload witness y : Nat}
    (h : positive xs s (packedAddress rawCtx t payload) witness y = true) :
    ∃ Γ target, contextView rawCtx = some Γ ∧ addressView y = some (Γ,t,target) ∧
      NumberedWindowPositivePathAlgorithm.positive (step xs s) (least s) Γ t payload witness target = true := by
  change addressRS (step xs s) (least s) (packedAddress rawCtx t payload) witness y = true at h
  unfold addressRS at h
  rw [literalView] at h
  cases hc : contextView rawCtx with
  | none => simp [hc] at h
  | some Γ =>
    cases ht : typeBit t with
    | false => simp [hc,ht] at h
    | true =>
      cases hy : addressView y with
      | none => simp [hc,ht,hy] at h
      | some v =>
        rcases v with ⟨targetCtx,targetType,target⟩
        have bits :
            Γ = targetCtx ∧ t = targetType ∧
              NumberedWindowPositivePathAlgorithm.positive
                (step xs s) (least s) Γ t payload witness target = true := by
          simpa [hc,ht,hy,Bool.and_eq_true,beq_iff_eq,and_assoc] using h
        obtain ⟨sameCtx,sameType,walks⟩ := bits
        subst targetCtx
        subst targetType
        refine ⟨Γ,target,?_,?_,walks⟩
        · first | exact hc | rfl
        · first | exact hy | rfl

theorem exact_LiteralAtomicAddressView : ExactLiteralAtomicAddressView := literalView
theorem exact_ConcreteAtomicAdvance : ExactConcreteAtomicAdvance := atomAdvance
theorem exact_ConcreteAtomicPositivePath : ExactConcreteAtomicPositivePath := atomPositivePath

theorem exact_ConcreteAtomicAddressPositive : ExactConcreteAtomicAddressPositive := by
  constructor
  · intro xs s rawCtx t n witness y h
    obtain ⟨Γ,target,ctx,v,walks⟩ := actualPath xs s h
    obtain ⟨endBottom,present,ownLeast,_⟩ := atomPositivePath.1 xs s Γ t t n witness target walks
    subst target
    refine ⟨?_,?_⟩
    · have same := (addressCoordinates v).1
      rw [bottomAddress,packedAddress,contextCode ctx]
      exact same
    · simp [scalar,v,canonical,present,ownLeast]
  · intro xs s rawCtx t witness y
    cases h : positive xs s (bottomAddress rawCtx t) witness y with
    | false => rfl
    | true =>
      obtain ⟨Γ,target,_,_,walks⟩ := actualPath xs s h
      rw [atomPositivePath.2 xs s Γ t t witness target] at walks
      cases walks

#print axioms exact_LiteralAtomicAddressView
#print axioms exact_ConcreteAtomicAdvance
#print axioms exact_ConcreteAtomicPositivePath
#print axioms exact_ConcreteAtomicAddressPositive
end LogicLineages.PersistentMarking.NumberedWindowAtomicPositiveChecks
