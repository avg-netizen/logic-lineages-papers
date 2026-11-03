module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedRelatedSubstitutionSupportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedRelatedSubstitutionProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication RecursiveComparison
open SourceExtendedSubstitution SourceExtendedSubstitutionSupportProof SourceExtendedRelatedSubstitution SourceExtendedRelatedSubstitutionSupportProof

theorem weakCovariance : ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop) (Γ Δ : List Ty) (theta eta : MarkedSubstitution Symbol arity Γ Δ) (H : EnvironmentsRelated above theta eta) (s t : Packed Symbol arity Γ), SourceExtendedComparison.Weak Symbol arity above Γ s t → SourceExtendedComparison.Weak Symbol arity above Δ (substitutePacked theta s) (substitutePacked eta t) := by
  intro Symbol arity above Γ Δ theta eta H s t h
  induction h using SourceExtendedComparison.Weak.rec
    (motive_2 := fun Γ s t _ => ∀ (Δ : List Ty) (theta eta : MarkedSubstitution Symbol arity Γ Δ) (H : EnvironmentsRelated above theta eta), SourceExtendedComparison.Strict Symbol arity above Δ (substitutePacked theta s) (substitutePacked eta t))
    (motive_3 := fun Γ ss ts _ => ∀ (Δ : List Ty) (theta eta : MarkedSubstitution Symbol arity Γ Δ) (H : EnvironmentsRelated above theta eta), SourceExtendedComparison.WeakMatch Symbol arity above Δ (ss.map (substitutePacked theta)) (ts.map (substitutePacked eta)))
    (motive_4 := fun Γ ss ts _ => ∀ (Δ : List Ty) (theta eta : MarkedSubstitution Symbol arity Γ Δ) (H : EnvironmentsRelated above theta eta), SourceExtendedComparison.StrictMultiset Symbol arity above Δ (ss.map (substitutePacked theta)) (ts.map (substitutePacked eta)))
    (motive_5 := fun Γ ss ts _ => ∀ (Δ : List Ty) (theta eta : MarkedSubstitution Symbol arity Γ Δ) (H : EnvironmentsRelated above theta eta), SourceExtendedComparison.ReplacementMatch Symbol arity above Δ (ss.map (substitutePacked theta)) (ts.map (substitutePacked eta)))
    generalizing Δ
  case var v => exact H _ v
  case abs s t hw ih =>
      apply SourceExtendedComparison.Weak.abs
      have H := ih _ (liftSubstitution theta) (liftSubstitution eta) (liftRelated above theta eta H _)
      simpa only [substitutePacked,substituteTerm] using H
  case fun_ f g ss ts matched he ht hp hm ih =>
      apply SourceExtendedComparison.Weak.fun_ f g (substituteArguments ss theta) (substituteArguments ts eta) (matched.map (substitutePacked eta)) he ht
      · rw [argumentListSubstitution]; exact hp.map (substitutePacked eta)
      · rw [argumentListSubstitution]; exact ih Δ theta eta H
  case put f ss t hw ih => exact .put f (substituteArguments ss theta) (substituteTerm t eta) (ih Δ theta eta H)
  case select f ss extraTypes extras types q r t suffix hmem happ hw ih =>
      apply SourceExtendedComparison.Weak.select f (substituteArguments ss theta) extraTypes (substituteArguments extras theta) types
        (substituteTerm q theta) (substituteTerm r theta) (substituteTerm t eta) suffix
      · rw [argumentListSubstitution,argumentListSubstitution,←List.map_append]
        exact List.mem_map.mpr ⟨_,hmem,rfl⟩
      · rw [←selfSubstitution]
        exact OrdinarySubstitutionStabilitySupportProof.successfulOriginalApply Symbol arity _ _ _ _ types q
          (selfArguments f ss extraTypes extras types) suffix r theta happ
      · exact ih Δ theta eta H
  case fAbs f ss extraTypes extras t hw ih =>
      simp only [substitutePacked,substituteTerm]
      apply SourceExtendedComparison.Weak.fAbs f (substituteArguments ss theta) extraTypes (substituteArguments extras theta)
        (substituteTerm t (liftSubstitution eta))
      have H := ih _ (liftSubstitution theta) (liftSubstitution eta) (liftRelated above theta eta H _)
      simpa only [substitutePacked,openMarkedSubstitution] using H
  case copy f g ss extraTypes extras ts ha hw ih =>
      apply SourceExtendedComparison.Weak.copy f g (substituteArguments ss theta) extraTypes (substituteArguments extras theta) (substituteArguments ts eta) ha
      intro p hp
      rw [argumentListSubstitution] at hp
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
      exact ih q hq Δ theta eta H
  case stat f g ss extraTypes extras ts he hm hw ihm ihw =>
      apply SourceExtendedComparison.Weak.stat f g (substituteArguments ss theta) extraTypes (substituteArguments extras theta) (substituteArguments ts eta) he
      · rw [argumentListSubstitution,argumentListSubstitution]; exact ihm Δ theta eta H
      · intro p hp
        rw [argumentListSubstitution] at hp
        obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
        exact ihw q hq Δ theta eta H
  case in_ f g ss ts typesS extrasS typesT extrasT matched he hp hm hx ihm ihx =>
      apply SourceExtendedComparison.Weak.in_ f g (substituteArguments ss theta) (substituteArguments ts eta)
        typesS (substituteArguments extrasS theta) typesT (substituteArguments extrasT eta) (matched.map (substitutePacked eta)) he
      · rw [argumentListSubstitution]; exact hp.map (substitutePacked eta)
      · rw [argumentListSubstitution]; exact ihm Δ theta eta H
      · rw [argumentListSubstitution,argumentListSubstitution]; exact ihx Δ theta eta H
  case marked1 f g ss typesS extrasS ts typesT extrasT hp hw ih =>
      apply SourceExtendedComparison.Weak.marked1 f g (substituteArguments ss theta) typesS (substituteArguments extrasS theta)
        (substituteArguments ts eta) typesT (substituteArguments extrasT eta) hp
      intro p hp'
      rw [argumentListSubstitution,argumentListSubstitution,←List.map_append] at hp'
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp'
      exact ih q hq Δ theta eta H
  case marked2 f g ss typesS extrasS ts typesT extrasT he hm hw ihm ihw =>
      apply SourceExtendedComparison.Weak.marked2 f g (substituteArguments ss theta) typesS (substituteArguments extrasS theta)
        (substituteArguments ts eta) typesT (substituteArguments extrasT eta) he
      · rw [argumentListSubstitution,argumentListSubstitution]; exact ihm Δ theta eta H
      · intro p hp'
        rw [argumentListSubstitution,argumentListSubstitution,←List.map_append] at hp'
        obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp'
        exact ihw q hq Δ theta eta H
  case dropMore f base types moreTypes extras more t hw ih =>
      simp only [substitutePacked,substituteTerm,SuccessfulApplicationPostProof.substituteAppend]
      exact .dropMore f _ types moreTypes _ _ _ (ih Δ theta eta H)
  case reorder f base typesS typesT extrasS extrasT t hp hw ih =>
      apply SourceExtendedComparison.Weak.reorder f _ typesS typesT _ _ _
      · rw [argumentListSubstitution,argumentListSubstitution]; exact hp.map _
      · exact ih Δ theta eta H
  case addPrefixCopies f base types copyTypes extras copies t hc hw ih =>
      apply SourceExtendedComparison.Weak.addPrefixCopies f _ types copyTypes _ (substituteArguments copies theta) _
      · exact copiesSubstitution f base extras copies hc theta
      · simpa only [substitutePacked,substituteTerm,SuccessfulApplicationPostProof.substituteAppend] using ih Δ theta eta H
  case prefixSelect f base extraTypes types extras copies q r t suffix hm hc ha hw ih =>
      apply SourceExtendedComparison.Weak.prefixSelect f (substituteArguments base theta) extraTypes types
        (substituteArguments extras theta) (substituteArguments copies theta) (substituteTerm q theta)
        (substituteTerm r theta) (substituteTerm t eta) suffix
      · rw [argumentListSubstitution,argumentListSubstitution,←List.map_append]
        exact List.mem_map.mpr ⟨_,hm,rfl⟩
      · exact copiesSubstitution f base extras copies hc theta
      · exact OrdinarySubstitutionStabilitySupportProof.successfulOriginalApply Symbol arity _ _ _ _ types q copies suffix r theta ha
      · exact ih Δ theta eta H
  case mark s r t hm hw ih Δ theta eta H =>
      apply SourceExtendedComparison.Strict.mark (substituteTerm s theta) (substituteTerm r theta) (substituteTerm t eta)
      · exact SuccessfulApplicationPostProof.strictMarkSubstitution Symbol arity _ _ _ s r theta hm
      · exact ih Δ theta eta H
  case nil => exact .nil
  case cons s t ss ts hw hm ihw ihm Δ theta eta H =>
      exact .cons _ _ _ _ (ihw Δ theta eta H) (ihm Δ theta eta H)
  case replace ss ts kept retained removed inserted hp hq hn hw hr ihw ihr Δ theta eta H =>
      apply SourceExtendedComparison.StrictMultiset.replace _ _ (kept.map (substitutePacked theta)) (retained.map (substitutePacked eta))
        (removed.map (substitutePacked theta)) (inserted.map (substitutePacked eta))
      · simpa only [List.map_append] using hp.map (substitutePacked theta)
      · simpa only [List.map_append] using hq.map (substitutePacked eta)
      · intro he
        exact hn (List.map_eq_nil_iff.mp he)
      · exact ihw Δ theta eta H
      · exact ihr Δ theta eta H
  case nil =>
      intros
      exact .nil _
  case cons =>
      intros
      rename_i Gamma removed s t rest hm hs hr ihs ihr Delta theta eta H
      exact .cons _ _ _ _ (List.mem_map.mpr ⟨s,hm,rfl⟩) (ihs Delta theta eta H) (ihr Delta theta eta H)

theorem strictCovariance : ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop) (Γ Δ : List Ty) (theta eta : MarkedSubstitution Symbol arity Γ Δ) (H : EnvironmentsRelated above theta eta) (s t : Packed Symbol arity Γ), SourceExtendedComparison.Strict Symbol arity above Γ s t → SourceExtendedComparison.Strict Symbol arity above Δ (substitutePacked theta s) (substitutePacked eta t) := by
  intro Symbol arity above Γ Δ theta eta H s t h
  cases h with
  | mark s r t hm hw =>
      apply SourceExtendedComparison.Strict.mark (substituteTerm s theta) (substituteTerm r theta) (substituteTerm t eta)
      · exact SuccessfulApplicationPostProof.strictMarkSubstitution Symbol arity _ _ _ s r theta hm
      · exact weakCovariance Symbol arity above Γ Δ theta eta H _ _ hw

theorem weakMatchCovariance : ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop) (Γ Δ : List Ty) (theta eta : MarkedSubstitution Symbol arity Γ Δ) (H : EnvironmentsRelated above theta eta) (ss ts : List (Packed Symbol arity Γ)), SourceExtendedComparison.WeakMatch Symbol arity above Γ ss ts → SourceExtendedComparison.WeakMatch Symbol arity above Δ (ss.map (substitutePacked theta)) (ts.map (substitutePacked eta)) := by
  intro Symbol arity above Γ Δ theta eta H ss
  induction ss with
  | nil => intro ts h; cases h; exact .nil
  | cons s ss ih =>
      intro ts h
      cases h with
      | cons _ t _ ts hw hm => exact .cons _ _ _ _ (weakCovariance Symbol arity above Γ Δ theta eta H _ _ hw) (ih ts hm)

theorem replacementMatchCovariance : ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop) (Γ Δ : List Ty) (theta eta : MarkedSubstitution Symbol arity Γ Δ) (H : EnvironmentsRelated above theta eta) (ss ts : List (Packed Symbol arity Γ)), SourceExtendedComparison.ReplacementMatch Symbol arity above Γ ss ts → SourceExtendedComparison.ReplacementMatch Symbol arity above Δ (ss.map (substitutePacked theta)) (ts.map (substitutePacked eta)) := by
  intro Symbol arity above Γ Δ theta eta H ss ts
  induction ts with
  | nil => intro h; exact .nil _
  | cons t ts ih =>
      intro h
      cases h with
      | cons _ s _ _ hs hst hr =>
          exact .cons _ _ _ _ (List.mem_map.mpr ⟨s,hs,rfl⟩) (strictCovariance Symbol arity above Γ Δ theta eta H _ _ hst) (ih hr)

theorem strictMultisetCovariance : ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop) (Γ Δ : List Ty) (theta eta : MarkedSubstitution Symbol arity Γ Δ) (H : EnvironmentsRelated above theta eta) (ss ts : List (Packed Symbol arity Γ)), SourceExtendedComparison.StrictMultiset Symbol arity above Γ ss ts → SourceExtendedComparison.StrictMultiset Symbol arity above Δ (ss.map (substitutePacked theta)) (ts.map (substitutePacked eta)) := by
  intro Symbol arity above Γ Δ theta eta H ss ts h
  cases h with
  | replace _ _ kept retained removed inserted hp hq hn hw hr =>
      apply SourceExtendedComparison.StrictMultiset.replace _ _ (kept.map (substitutePacked theta)) (retained.map (substitutePacked eta))
        (removed.map (substitutePacked theta)) (inserted.map (substitutePacked eta))
      · simpa only [List.map_append] using hp.map (substitutePacked theta)
      · simpa only [List.map_append] using hq.map (substitutePacked eta)
      · intro he
        exact hn (List.map_eq_nil_iff.mp he)
      · exact weakMatchCovariance Symbol arity above Γ Δ theta eta H _ _ hw
      · exact replacementMatchCovariance Symbol arity above Γ Δ theta eta H _ _ hr

theorem actualJointRelatedCovariance : SourceExtendedRelatedSubstitutionTargets.ActualJointRelatedCovariance := by
  intro Symbol arity above
  exact ⟨fun Γ s t h Δ theta eta H => weakCovariance Symbol arity above Γ Δ theta eta H s t h,
    fun Γ s t h Δ theta eta H => strictCovariance Symbol arity above Γ Δ theta eta H s t h,
    fun Γ ss ts h Δ theta eta H => weakMatchCovariance Symbol arity above Γ Δ theta eta H ss ts h,
    fun Γ ss ts h Δ theta eta H => strictMultisetCovariance Symbol arity above Γ Δ theta eta H ss ts h,
    fun Γ ss ts h Δ theta eta H => replacementMatchCovariance Symbol arity above Γ Δ theta eta H ss ts h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedRelatedSubstitutionProof
