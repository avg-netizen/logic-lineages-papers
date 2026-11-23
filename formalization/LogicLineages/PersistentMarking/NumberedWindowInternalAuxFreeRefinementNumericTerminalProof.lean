module
public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxBottomRefinementNumericTargets
import LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationReductionChecks
import LogicLineages.PersistentMarking.NumberedWindowAtomicPositiveAddressSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedEmitterAddressProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAuxFreeRefinementNumericTerminalProof
open NumberedWindowInternalAuxBottomRefinementNumericTargets
open NumberedWindowAtomicApplicationReductionChecks (exact_AtomicAuxPositivePath)
open NumberedWindowAtomicApplicationTargets (auxRaw AtomHead)
open NumberedWindowAtomicPositiveTargets (packedAddress bottomAddress)
open NumberedWindowAtomicPositiveAddressSyntaxProof (literalView contextCode)
open NumberedWindowAtomicRawStep (bottomRaw freeRaw)
open NumberedWindowAtomicRawStepChecks (exact_AtomicRawFields)
open NumberedWindowFieldAlgorithm (unpackNode)
open NumberedWindowInternalFreshProbeParsedEmitterAddressProof (addressCoordinates)
open NumberedWindowAddressAlgorithm (addressView contextView typeBit)
open NumberedWindowConcreteCheckers (step positive)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings scalar least canonical admitted)
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

/-- Free-headed positive targets retain the raw context and result, and have
either the exact whole bottom or an actual bottom-function application. The
second alternative exposes the original admitted raw endpoint and least
report; it does not silently identify the raw and visible right arguments. -/
theorem exact_ConcreteAuxFreeAddressPositive (xs : Entries) (s : Settings)
    (c dom cod stored name arg witness y : Nat)
    (h : positive xs s (packedAddress c cod (auxRaw dom cod (freeRaw stored name) arg)) witness y = true) :
    (y = bottomAddress c cod ∧ scalar s y = true) ∨
    (∃ Γ rawArg visibleArg, contextView c = some Γ ∧
      y = packedAddress c cod (auxRaw dom cod (bottomRaw stored) visibleArg) ∧
      admitted s Γ cod (auxRaw dom cod (bottomRaw stored) rawArg) = true ∧
      least s Γ cod (auxRaw dom cod (bottomRaw stored) rawArg) =
        some (auxRaw dom cod (bottomRaw stored) visibleArg)) := by
  obtain ⟨Γ,target,ctx,view,walked⟩ :=
    fromAddress xs s (c := c) (e := cod) (k := auxRaw dom cod (freeRaw stored name) arg) h
  have rawAddress : y = packedAddress c cod target := by
    rw [contextCode ctx]
    exact (addressCoordinates view).1
  have wholeBottom (rawTarget : Nat) (rawBottom : rawTarget = bottomRaw cod)
      (visibleBottom : target = bottomRaw cod) (ha : admitted s Γ cod rawTarget = true)
      (hl : least s Γ cod rawTarget = some target) :
      y = bottomAddress c cod ∧ scalar s y = true := by
    constructor
    · simpa only [bottomAddress,visibleBottom] using rawAddress
    · rw [rawBottom] at ha hl
      simp [scalar,view,canonical,visibleBottom,ha,hl]
  have actual := exact_AtomicAuxPositivePath xs s Γ cod dom cod (freeRaw stored name) arg witness target
    (AtomHead.free stored name) walked
  rcases actual with ⟨_,_,_,used⟩ | ⟨_,_,stored',_,_,_,_,_,_,_,used,_⟩
  · obtain ⟨_,_,rawTarget,rawArg,_,_,_,ha,_,hl,_,shape⟩ := used
    rcases shape with ⟨_,rawBottom,visibleBottom⟩ |
      ⟨stored',name',_,visibleArg,same,_,_,rawEq,visEq,_⟩
    · exact Or.inl (wholeBottom rawTarget rawBottom visibleBottom ha hl)
    · have parsed := congrArg unpackNode same
      rw [(exact_AtomicRawFields.1 stored name).1,
        (exact_AtomicRawFields.1 stored' name').1] at parsed
      have fields := congrArg Prod.snd (Option.some.inj parsed)
      have sameStored : stored = stored' := congrArg (fun ls : List Nat => ls.headD 0) fields
      subst stored'
      exact Or.inr ⟨Γ,rawArg,visibleArg,ctx,rawAddress.trans (congrArg (packedAddress c cod) visEq),
        by simpa only [rawEq] using ha,by simpa only [rawEq,visEq] using hl⟩
  · obtain ⟨_,_,rawTarget,_,_,_,_,ha,_,hl,_,shape⟩ := used
    rcases shape with ⟨_,rawBottom,visibleBottom⟩ | ⟨t,n,_,_,bad,_⟩
    · exact Or.inl (wholeBottom rawTarget rawBottom visibleBottom ha hl)
    · exact False.elim (exact_AtomicRawFields.2.2.1 t n stored' bad.symm)

#print axioms exact_ConcreteAuxFreeAddressPositive
end LogicLineages.PersistentMarking.NumberedWindowInternalAuxFreeRefinementNumericTerminalProof
