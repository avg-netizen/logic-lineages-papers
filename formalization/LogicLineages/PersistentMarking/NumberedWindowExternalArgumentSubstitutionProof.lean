import LogicLineages.PersistentMarking.NumberedWindowExternalPrimaryShiftProof
import LogicLineages.PersistentMarking.NumberedWindowExternalSubstitutionChecks

namespace LogicLineages.PersistentMarking.NumberedWindowExternalArgumentSubstitutionProof
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowPrimary NumberedWindowSimulationData
open NumberedWindowExternalSubstitutionTargets NumberedWindowExternalArgumentSubstitutionTargets
open NumberedWindowPreservationBoundProof (Compatible push one)
open NumberedWindowPreservationGuardProof
open NumberedWindowApplicationDomainProof (annotation rootInWindow)
open NumberedWindowNumberedDomainProof (ArgsGuard parts)

private theorem boundCase {S K E D σ ρ a b d i} (ha : Typed E a σ)
    (hp : Primary S K E σ a b) (hs : Spine.ShiftCompatible d 0 E D)
    (ht : Typed D (substitute (.cons a .nil) d (.bound ρ i)) ρ) :
    Primary S K D ρ (substitute (.cons a .nil) d (.bound ρ i))
      (substitute (.cons b .nil) d (.bound ρ i)) := by
  by_cases hi : i < d
  · simp only [substitute, hi, if_true] at ht ⊢
    exact .refl ht
  · by_cases he : i = d
    · subst i
      simp only [substitute, Nat.lt_irrefl, if_false, Nat.sub_self, NArgs.get] at ht ⊢
      have hType : ρ = σ := (annotation ht).symm.trans
        ((NumberedWindowApplicationShiftProof.shape a d 0).1.trans (annotation ha))
      subst ρ
      exact NumberedWindowExternalPrimaryShiftProof.lexical S K E D σ a b d 0 hs hp
    · have hIndex : i - d ≠ 0 := by omega
      simp only [substitute, hi, if_false, NumberedWindowBindingBaseProof.singletonPast _ _ hIndex] at ht ⊢
      exact .refl ht

private theorem pushShift {E D : Spine.BoundContext} {d : Nat} (ρ : Ty)
    (h : Spine.ShiftCompatible d 0 E D) : Spine.ShiftCompatible (d + 1) 0 E (D.push ρ) := by
  intro i t hi
  have hImage := h i t hi
  simp only [Nat.not_lt_zero, if_false] at hImage ⊢
  rw [← Nat.add_assoc, Nat.add_one]
  change D (i + d) = some t
  exact hImage

section
variable {S : Spine.Signature} {K : List Ty} {E : Spine.BoundContext} {σ : Ty} {a b : NTerm}

mutual
private theorem substituteTerm (hk : DecisionSourceUniverse.Closed K) (ha : Typed E a σ)
    (hp : Primary S K E σ a b) (d : Nat) (C D : Spine.BoundContext)
    (hs : Spine.ShiftCompatible d 0 E D) (hl : Compatible S K (.cons a .nil) d C D)
    (hr : Compatible S K (.cons b .nil) d C D) (q : NTerm) (τ : Ty) (hq : InWindow S K C τ q) :
    Primary S K D τ (substitute (.cons a .nil) d q) (substitute (.cons b .nil) d q) := by
  have ht := hq.1
  cases ht with
  | free => exact .refl .free
  | bound hi => exact boundCase ha hp hs (hl _ _ hi (rootInWindow hq)).1
  | lam _ =>
    exact .lam (substituteTerm hk ha hp (d + 1) _ _ (pushShift _ hs)
      (push hk hl) (push hk hr) _ _ (lamBody hq))
  | bottom => exact .refl .bottom
  | ordinary hBase =>
    exact .ordinaryArguments (substituteBase hk ha hp d C D hs hl hr _ _ hBase (ordinaryParts hq).2.2)
  | numbered hBase hExtra =>
    obtain ⟨_, _, _, hbs, hes⟩ := parts hq
    have hLeftExtra := (NumberedWindowPreservationSubstitutionProof.extras S K hk _ d C D _ hExtra hes hl).1
    have hRightBase := (NumberedWindowPreservationSubstitutionProof.base S K hk _ d C D _ _ hBase hbs hr).1
    have hBases := substituteBase hk ha hp d C D hs hl hr _ _ hBase hbs
    obtain ⟨_, hExtras⟩ := substituteExtras hk ha hp d C D hs hl hr _ hExtra hes
    exact .trans (.numberedBase hBases hLeftExtra) (.numberedExtras hRightBase hExtras)
  | auxApp _ _ =>
    obtain ⟨hf, hu⟩ := appParts hq
    have hLeftArg := (NumberedWindowPreservationSubstitutionProof.term S K hk _ d C D _ _ hu hl).1
    have hRightFn := (NumberedWindowPreservationSubstitutionProof.term S K hk _ d C D _ _ hf hr).1
    exact .trans (.appFunction (substituteTerm hk ha hp d C D hs hl hr _ _ hf) hLeftArg)
      (.appArgument hRightFn (substituteTerm hk ha hp d C D hs hl hr _ _ hu))
termination_by sizeOf q

private theorem substituteBase (hk : DecisionSourceUniverse.Closed K) (ha : Typed E a σ)
    (hp : Primary S K E σ a b) (d : Nat) (C D : Spine.BoundContext)
    (hs : Spine.ShiftCompatible d 0 E D) (hl : Compatible S K (.cons a .nil) d C D)
    (hr : Compatible S K (.cons b .nil) d C D) (xs : NArgs) (types : List Ty)
    (ht : BaseTyped C xs types) (hg : ArgsGuard S K xs) :
    OrderedPrimary S K D types (substituteArgs (.cons a .nil) d xs) (substituteArgs (.cons b .nil) d xs) := by
  cases ht with
  | nil => exact .nil
  | cons hValue hRest =>
    obtain ⟨hv, ht⟩ := consParts hg
    exact .cons (substituteTerm hk ha hp d C D hs hl hr _ _ ⟨hValue, hv⟩)
      (substituteBase hk ha hp d C D hs hl hr _ _ hRest ht)
termination_by sizeOf xs

private theorem substituteExtras (hk : DecisionSourceUniverse.Closed K) (ha : Typed E a σ)
    (hp : Primary S K E σ a b) (d : Nat) (C D : Spine.BoundContext)
    (hs : Spine.ShiftCompatible d 0 E D) (hl : Compatible S K (.cons a .nil) d C D)
    (hr : Compatible S K (.cons b .nil) d C D) (xs : NArgs)
    (ht : ExtrasTyped C xs) (hg : ArgsGuard S K xs) :
    ∃ types, OrderedPrimary S K D types (substituteArgs (.cons a .nil) d xs) (substituteArgs (.cons b .nil) d xs) := by
  cases ht with
  | nil => exact ⟨[], .nil⟩
  | cons hValue hRest =>
    obtain ⟨hv, ht⟩ := consParts hg
    obtain ⟨_, hTail⟩ := substituteExtras hk ha hp d C D hs hl hr _ hRest ht
    exact ⟨_, .cons (substituteTerm hk ha hp d C D hs hl hr _ _ ⟨hValue, hv⟩) hTail⟩
termination_by sizeOf xs
end
end

theorem argument : LiteralArgumentClassSubstitution := by
  intro S K C σ τ hk body a b hEq
  have hp := NumberedWindowExternalNeutralPrimaryProof.primaryOfClassEquality a b hEq
  have hZero : Spine.ShiftCompatible 0 0 C C := by
    intro i t hi
    simpa only [Nat.not_lt_zero, if_false, Nat.add_zero] using hi
  exact Quot.sound (substituteTerm hk a.property.1 hp 0 _ C hZero (one hk a.property)
    (one hk b.property) body.val τ body.property)

theorem instanceCongr : LiteralInstanceClassSubstitution := by
  intro S K C σ τ hk body other a b hBody hArg
  exact ((NumberedWindowExternalSubstitutionChecks.exact_LiteralBodyClassSubstitution
    S K C σ τ hk body other a).2 hBody).trans (argument S K C σ τ hk other a b hArg)

end LogicLineages.PersistentMarking.NumberedWindowExternalArgumentSubstitutionProof
