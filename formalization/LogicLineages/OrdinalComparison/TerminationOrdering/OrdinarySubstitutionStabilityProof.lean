module
public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinarySubstitutionStabilitySupportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OrdinarySubstitutionStabilityProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication RecursiveComparison
open OrdinarySubstitutionStability OrdinarySubstitutionStabilitySupportProof

theorem weakCovariance : ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop) (Γ Δ : List Ty) (theta : Substitution Symbol arity Γ Δ) (s t : Packed Symbol arity Γ), Weak Symbol arity above Γ s t → Weak Symbol arity above Δ (substitutePacked theta s) (substitutePacked theta t) := by
  intro Symbol arity above Γ Δ theta s t h
  induction h using Weak.rec
    (motive_2 := fun Γ s t _ => ∀ (Δ : List Ty) (theta : Substitution Symbol arity Γ Δ), Strict Symbol arity above Δ (substitutePacked theta s) (substitutePacked theta t))
    (motive_3 := fun Γ ss ts _ => ∀ (Δ : List Ty) (theta : Substitution Symbol arity Γ Δ), WeakMatch Symbol arity above Δ (ss.map (substitutePacked theta)) (ts.map (substitutePacked theta)))
    (motive_4 := fun Γ ss ts _ => ∀ (Δ : List Ty) (theta : Substitution Symbol arity Γ Δ), StrictMultiset Symbol arity above Δ (ss.map (substitutePacked theta)) (ts.map (substitutePacked theta)))
    (motive_5 := fun Γ ss ts _ => ∀ (Δ : List Ty) (theta : Substitution Symbol arity Γ Δ), ReplacementMatch Symbol arity above Δ (ss.map (substitutePacked theta)) (ts.map (substitutePacked theta)))
    generalizing Δ
  case var v => exact RecursiveComparisonProof.literalOrdinaryReflexivity Symbol arity above Δ _ (theta v)
  case abs s t hw ih =>
      apply Weak.abs
      have H := ih _ (Substitution.lift theta)
      simpa only [substitutePacked,substituteTerm,liftMap] using H
  case fun_ f g ss ts matched he ht hp hm ih =>
      apply Weak.fun_ f g (substituteArguments ss (markedMap theta)) (substituteArguments ts (markedMap theta)) (matched.map (substitutePacked theta)) he ht
      · rw [argumentListSubstitution]; exact hp.map _
      · rw [argumentListSubstitution]; exact ih Δ theta
  case put f ss t hw ih => exact .put f (substituteArguments ss (markedMap theta)) (substituteTerm t (markedMap theta)) (ih Δ theta)
  case select f ss extraTypes extras types q r t suffix hmem happ hw ih =>
      apply Weak.select f (substituteArguments ss (markedMap theta)) extraTypes (substituteArguments extras (markedMap theta)) types
        (substituteTerm q (markedMap theta)) (substituteTerm r (markedMap theta)) (substituteTerm t (markedMap theta)) suffix
      · rw [argumentListSubstitution,argumentListSubstitution,←List.map_append]
        exact List.mem_map.mpr ⟨_,hmem,rfl⟩
      · rw [←selfSubstitution]
        exact successfulOriginalApply Symbol arity _ _ _ _ types q
          (selfArguments f ss extraTypes extras types) suffix r (markedMap theta) happ
      · exact ih Δ theta
  case fAbs f ss extraTypes extras t hw ih =>
      simp only [substitutePacked,substituteTerm,← liftMap]
      apply Weak.fAbs f (substituteArguments ss (markedMap theta)) extraTypes (substituteArguments extras (markedMap theta))
        (substituteTerm t (markedMap (Substitution.lift theta)))
      have H := ih _ (Substitution.lift theta)
      simpa only [substitutePacked,openMarkedSubstitution] using H
  case copy f g ss extraTypes extras ts ha hw ih =>
      apply Weak.copy f g (substituteArguments ss (markedMap theta)) extraTypes (substituteArguments extras (markedMap theta)) (substituteArguments ts (markedMap theta)) ha
      intro p hp
      rw [argumentListSubstitution] at hp
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
      exact ih q hq Δ theta
  case stat f g ss extraTypes extras ts he hm hw ihm ihw =>
      apply Weak.stat f g (substituteArguments ss (markedMap theta)) extraTypes (substituteArguments extras (markedMap theta)) (substituteArguments ts (markedMap theta)) he
      · rw [argumentListSubstitution,argumentListSubstitution]; exact ihm Δ theta
      · intro p hp
        rw [argumentListSubstitution] at hp
        obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
        exact ihw q hq Δ theta
  case mark s r t hm hw ih Δ theta =>
      apply Strict.mark (substituteTerm s (markedMap theta)) (substituteTerm r (markedMap theta)) (substituteTerm t (markedMap theta))
      · exact SuccessfulApplicationPostProof.strictMarkSubstitution Symbol arity _ _ _ s r (markedMap theta) hm
      · exact ih Δ theta
  case nil => exact .nil
  case cons s t ss ts hw hm ihw ihm Δ theta =>
      exact .cons _ _ _ _ (ihw Δ theta) (ihm Δ theta)
  case replace ss ts kept retained removed inserted hp hq hn hw hr ihw ihr Δ theta =>
      apply StrictMultiset.replace _ _ (kept.map (substitutePacked theta)) (retained.map (substitutePacked theta))
        (removed.map (substitutePacked theta)) (inserted.map (substitutePacked theta))
      · simpa only [List.map_append] using hp.map (substitutePacked theta)
      · simpa only [List.map_append] using hq.map (substitutePacked theta)
      · intro he
        exact hn (List.map_eq_nil_iff.mp he)
      · exact ihw Δ theta
      · exact ihr Δ theta
  case nil removed Δ =>
      intro theta
      exact .nil _
  case cons removed s t rest hs hst hr ihst ihr Δ =>
      intro theta
      exact .cons _ _ _ _ (List.mem_map.mpr ⟨s,hs,rfl⟩) (ihst Δ theta) (ihr Δ theta)

theorem strictCovariance : ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop) (Γ Δ : List Ty) (theta : Substitution Symbol arity Γ Δ) (s t : Packed Symbol arity Γ), Strict Symbol arity above Γ s t → Strict Symbol arity above Δ (substitutePacked theta s) (substitutePacked theta t) := by
  intro Symbol arity above Γ Δ theta s t h
  cases h with
  | mark s r t hm hw =>
      apply Strict.mark (substituteTerm s (markedMap theta)) (substituteTerm r (markedMap theta)) (substituteTerm t (markedMap theta))
      · exact SuccessfulApplicationPostProof.strictMarkSubstitution Symbol arity _ _ _ s r (markedMap theta) hm
      · exact weakCovariance Symbol arity above Γ Δ theta _ _ hw

theorem weakMatchCovariance : ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop) (Γ Δ : List Ty) (theta : Substitution Symbol arity Γ Δ) (ss ts : List (Packed Symbol arity Γ)), WeakMatch Symbol arity above Γ ss ts → WeakMatch Symbol arity above Δ (ss.map (substitutePacked theta)) (ts.map (substitutePacked theta)) := by
  intro Symbol arity above Γ Δ theta ss
  induction ss with
  | nil => intro ts h; cases h; exact .nil
  | cons s ss ih =>
      intro ts h
      cases h with
      | cons _ t _ ts hw hm => exact .cons _ _ _ _ (weakCovariance Symbol arity above Γ Δ theta _ _ hw) (ih ts hm)

theorem replacementMatchCovariance : ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop) (Γ Δ : List Ty) (theta : Substitution Symbol arity Γ Δ) (ss ts : List (Packed Symbol arity Γ)), ReplacementMatch Symbol arity above Γ ss ts → ReplacementMatch Symbol arity above Δ (ss.map (substitutePacked theta)) (ts.map (substitutePacked theta)) := by
  intro Symbol arity above Γ Δ theta ss ts
  induction ts with
  | nil => intro h; exact .nil _
  | cons t ts ih =>
      intro h
      cases h with
      | cons _ s _ _ hs hst hr =>
          exact .cons _ _ _ _ (List.mem_map.mpr ⟨s,hs,rfl⟩) (strictCovariance Symbol arity above Γ Δ theta _ _ hst) (ih hr)

theorem strictMultisetCovariance : ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop) (Γ Δ : List Ty) (theta : Substitution Symbol arity Γ Δ) (ss ts : List (Packed Symbol arity Γ)), StrictMultiset Symbol arity above Γ ss ts → StrictMultiset Symbol arity above Δ (ss.map (substitutePacked theta)) (ts.map (substitutePacked theta)) := by
  intro Symbol arity above Γ Δ theta ss ts h
  cases h with
  | replace _ _ kept retained removed inserted hp hq hn hw hr =>
      apply StrictMultiset.replace _ _ (kept.map (substitutePacked theta)) (retained.map (substitutePacked theta))
        (removed.map (substitutePacked theta)) (inserted.map (substitutePacked theta))
      · simpa only [List.map_append] using hp.map (substitutePacked theta)
      · simpa only [List.map_append] using hq.map (substitutePacked theta)
      · intro he
        exact hn (List.map_eq_nil_iff.mp he)
      · exact weakMatchCovariance Symbol arity above Γ Δ theta _ _ hw
      · exact replacementMatchCovariance Symbol arity above Γ Δ theta _ _ hr

theorem actualJointStability : OrdinarySubstitutionStabilityTargets.ActualJointStability := by
  intro Symbol arity above
  exact ⟨fun Γ s t h Δ theta => weakCovariance Symbol arity above Γ Δ theta s t h,
    fun Γ s t h Δ theta => strictCovariance Symbol arity above Γ Δ theta s t h,
    fun Γ ss ts h Δ theta => weakMatchCovariance Symbol arity above Γ Δ theta ss ts h,
    fun Γ ss ts h Δ theta => strictMultisetCovariance Symbol arity above Γ Δ theta ss ts h,
    fun Γ ss ts h Δ theta => replacementMatchCovariance Symbol arity above Γ Δ theta ss ts h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.OrdinarySubstitutionStabilityProof
