module
public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxBottomRefinementNumericTargets
import LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationReductionChecks
import LogicLineages.PersistentMarking.NumberedWindowAtomicPositiveAddressSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedEmitterAddressProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAuxBottomRefinementNumericTerminalProof
open NumberedWindowInternalAuxBottomRefinementNumericTargets
open NumberedWindowAtomicApplicationReductionChecks (exact_AtomicAuxPositivePath)
open NumberedWindowAtomicApplicationTargets (auxRaw AtomHead)
open NumberedWindowAtomicPositiveTargets (packedAddress bottomAddress)
open NumberedWindowAtomicPositiveAddressSyntaxProof (literalView contextCode)
open NumberedWindowAtomicRawStep (bottomRaw)
open NumberedWindowAtomicRawStepChecks (exact_AtomicRawFields)
open NumberedWindowInternalFreshProbeParsedEmitterAddressProof (addressCoordinates)
open NumberedWindowAddressAlgorithm (addressView contextView typeBit)
open NumberedWindowConcreteCheckers (step positive)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings scalar least canonical)
open NumberedWindowPositivePathAlgorithm (addressRS)

/-- The same original address decoding and shared context/annotation
test; no claim that the raw input/output were independently canonical. -/
private theorem fromAddress (xs : Entries) (s : Settings) {c e k witness y : Nat}
    (h : positive xs s (packedAddress c e k) witness y = true) :
    ∃ Γ target, contextView c = some Γ ∧ addressView y = some (Γ,e,target) ∧
      NumberedWindowPositivePathAlgorithm.positive (step xs s) (least s) Γ e k witness target = true := by
  change addressRS (step xs s) (least s) (packedAddress c e k) witness y = true at h
  unfold addressRS at h
  rw [literalView] at h
  cases hC : contextView c with
  | none => simp [hC] at h
  | some Γ =>
    cases hT : typeBit e with
    | false => simp [hC,hT] at h
    | true =>
      cases hy : addressView y with
      | none => simp [hC,hT,hy] at h
      | some v =>
        rcases v with ⟨otherCtx,otherType,target⟩
        have bits : Γ = otherCtx ∧ e = otherType ∧
            NumberedWindowPositivePathAlgorithm.positive (step xs s) (least s) Γ e k witness target = true := by
          simpa [hC,hT,hy,Bool.and_eq_true,beq_iff_eq,and_assoc] using h
        obtain ⟨sameC,sameT,walked⟩ := bits
        subst otherCtx
        subst otherType
        refine ⟨Γ,target,?_,?_,walked⟩
        · first | exact hC | rfl
        · first | exact hy | rfl

theorem exactTerminal : ExactConcreteAuxBottomAddressPositive := by
  intro xs s c dom cod stored arg witness y accepted
  obtain ⟨Γ,target,ctx,view,walked⟩ :=
    fromAddress xs s (c := c) (e := cod) (k := auxRaw dom cod (bottomRaw stored) arg) accepted
  have actual := exact_AtomicAuxPositivePath xs s Γ cod dom cod (bottomRaw stored) arg witness target
    (AtomHead.bottom stored) walked
  rcases actual with ⟨hop,unpacked,_,used⟩ | ⟨_,_,t,n,_,bad,_⟩
  · have keep := used
    obtain ⟨_,_,rawTarget,_,_,_,_,admitted,_,lastLeast,_,shape⟩ := used
    rcases shape with ⟨_,rawBottom,visibleBottom⟩ | ⟨t,n,_,_,bad,_⟩
    · subst rawTarget
      subst target
      refine ⟨Γ,hop,ctx,unpacked,keep,?_,admitted,lastLeast,?_⟩
      · have same := (addressCoordinates view).1
        rw [bottomAddress,packedAddress,contextCode ctx]
        exact same
      · simp [scalar,view,canonical,admitted,lastLeast]
    · exact False.elim (exact_AtomicRawFields.2.2.1 t n stored bad.symm)
  · exact False.elim (exact_AtomicRawFields.2.2.1 t n stored bad.symm)

end LogicLineages.PersistentMarking.NumberedWindowInternalAuxBottomRefinementNumericTerminalProof
