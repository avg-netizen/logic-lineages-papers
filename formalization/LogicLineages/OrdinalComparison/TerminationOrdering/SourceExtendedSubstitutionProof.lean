module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedSubstitutionSupportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedSubstitutionProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication RecursiveComparison
open SourceExtendedSubstitution SourceExtendedSubstitutionSupportProof

theorem weakCovariance : ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop) (Γ Δ : List Ty) (theta : MarkedSubstitution Symbol arity Γ Δ) (s t : Packed Symbol arity Γ), SourceExtendedComparison.Weak Symbol arity above Γ s t → SourceExtendedComparison.Weak Symbol arity above Δ (substitutePacked theta s) (substitutePacked theta t) := by
  intro Symbol arity above Γ Δ theta s t h
  induction h using SourceExtendedComparison.Weak.rec
    (motive_2 := fun Γ s t _ => ∀ (Δ : List Ty) (theta : MarkedSubstitution Symbol arity Γ Δ), SourceExtendedComparison.Strict Symbol arity above Δ (substitutePacked theta s) (substitutePacked theta t))
    (motive_3 := fun Γ ss ts _ => ∀ (Δ : List Ty) (theta : MarkedSubstitution Symbol arity Γ Δ), SourceExtendedComparison.WeakMatch Symbol arity above Δ (ss.map (substitutePacked theta)) (ts.map (substitutePacked theta)))
    (motive_4 := fun Γ ss ts _ => ∀ (Δ : List Ty) (theta : MarkedSubstitution Symbol arity Γ Δ), SourceExtendedComparison.StrictMultiset Symbol arity above Δ (ss.map (substitutePacked theta)) (ts.map (substitutePacked theta)))
    (motive_5 := fun Γ ss ts _ => ∀ (Δ : List Ty) (theta : MarkedSubstitution Symbol arity Γ Δ), SourceExtendedComparison.ReplacementMatch Symbol arity above Δ (ss.map (substitutePacked theta)) (ts.map (substitutePacked theta)))
    generalizing Δ
  case var v => exact reflexiveTerm above (theta v)
  case abs s t hw ih =>
      apply SourceExtendedComparison.Weak.abs
      have H := ih _ (liftSubstitution theta)
      simpa only [substitutePacked,substituteTerm] using H
  case fun_ f g ss ts matched he ht hp hm ih =>
      apply SourceExtendedComparison.Weak.fun_ f g (substituteArguments ss theta) (substituteArguments ts theta) (matched.map (substitutePacked theta)) he ht
      · rw [argumentListSubstitution]; exact hp.map _
      · rw [argumentListSubstitution]; exact ih Δ theta
  case put f ss t hw ih => exact .put f (substituteArguments ss theta) (substituteTerm t theta) (ih Δ theta)
  case select f ss extraTypes extras types q r t suffix hmem happ hw ih =>
      apply SourceExtendedComparison.Weak.select f (substituteArguments ss theta) extraTypes (substituteArguments extras theta) types
        (substituteTerm q theta) (substituteTerm r theta) (substituteTerm t theta) suffix
      · rw [argumentListSubstitution,argumentListSubstitution,←List.map_append]
        exact List.mem_map.mpr ⟨_,hmem,rfl⟩
      · rw [←selfSubstitution]
        exact OrdinarySubstitutionStabilitySupportProof.successfulOriginalApply Symbol arity _ _ _ _ types q
          (selfArguments f ss extraTypes extras types) suffix r theta happ
      · exact ih Δ theta
  case fAbs f ss extraTypes extras t hw ih =>
      simp only [substitutePacked,substituteTerm]
      apply SourceExtendedComparison.Weak.fAbs f (substituteArguments ss theta) extraTypes (substituteArguments extras theta)
        (substituteTerm t (liftSubstitution theta))
      have H := ih _ (liftSubstitution theta)
      simpa only [substitutePacked,openMarkedSubstitution] using H
  case copy f g ss extraTypes extras ts ha hw ih =>
      apply SourceExtendedComparison.Weak.copy f g (substituteArguments ss theta) extraTypes (substituteArguments extras theta) (substituteArguments ts theta) ha
      intro p hp
      rw [argumentListSubstitution] at hp
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
      exact ih q hq Δ theta
  case stat f g ss extraTypes extras ts he hm hw ihm ihw =>
      apply SourceExtendedComparison.Weak.stat f g (substituteArguments ss theta) extraTypes (substituteArguments extras theta) (substituteArguments ts theta) he
      · rw [argumentListSubstitution,argumentListSubstitution]; exact ihm Δ theta
      · intro p hp
        rw [argumentListSubstitution] at hp
        obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
        exact ihw q hq Δ theta
  case in_ f g ss ts typesS extrasS typesT extrasT matched he hp hm hx ihm ihx =>
      apply SourceExtendedComparison.Weak.in_ f g (substituteArguments ss theta) (substituteArguments ts theta)
        typesS (substituteArguments extrasS theta) typesT (substituteArguments extrasT theta) (matched.map (substitutePacked theta)) he
      · rw [argumentListSubstitution]; exact hp.map _
      · rw [argumentListSubstitution]; exact ihm Δ theta
      · rw [argumentListSubstitution,argumentListSubstitution]; exact ihx Δ theta
  case marked1 f g ss typesS extrasS ts typesT extrasT hp hw ih =>
      apply SourceExtendedComparison.Weak.marked1 f g (substituteArguments ss theta) typesS (substituteArguments extrasS theta)
        (substituteArguments ts theta) typesT (substituteArguments extrasT theta) hp
      intro p hp'
      rw [argumentListSubstitution,argumentListSubstitution,←List.map_append] at hp'
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp'
      exact ih q hq Δ theta
  case marked2 f g ss typesS extrasS ts typesT extrasT he hm hw ihm ihw =>
      apply SourceExtendedComparison.Weak.marked2 f g (substituteArguments ss theta) typesS (substituteArguments extrasS theta)
        (substituteArguments ts theta) typesT (substituteArguments extrasT theta) he
      · rw [argumentListSubstitution,argumentListSubstitution]; exact ihm Δ theta
      · intro p hp'
        rw [argumentListSubstitution,argumentListSubstitution,←List.map_append] at hp'
        obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp'
        exact ihw q hq Δ theta
  case dropMore f base types moreTypes extras more t hw ih =>
      simp only [substitutePacked,substituteTerm,SuccessfulApplicationPostProof.substituteAppend]
      exact .dropMore f _ types moreTypes _ _ _ (ih Δ theta)
  case reorder f base typesS typesT extrasS extrasT t hp hw ih =>
      apply SourceExtendedComparison.Weak.reorder f _ typesS typesT _ _ _
      · rw [argumentListSubstitution,argumentListSubstitution]; exact hp.map _
      · exact ih Δ theta
  case addPrefixCopies f base types copyTypes extras copies t hc hw ih =>
      apply SourceExtendedComparison.Weak.addPrefixCopies f _ types copyTypes _ (substituteArguments copies theta) _
      · exact copiesSubstitution f base extras copies hc theta
      · simpa only [substitutePacked,substituteTerm,SuccessfulApplicationPostProof.substituteAppend] using ih Δ theta
  case prefixSelect f base extraTypes types extras copies q r t suffix hm hc ha hw ih =>
      apply SourceExtendedComparison.Weak.prefixSelect f (substituteArguments base theta) extraTypes types
        (substituteArguments extras theta) (substituteArguments copies theta) (substituteTerm q theta)
        (substituteTerm r theta) (substituteTerm t theta) suffix
      · rw [argumentListSubstitution,argumentListSubstitution,←List.map_append]
        exact List.mem_map.mpr ⟨_,hm,rfl⟩
      · exact copiesSubstitution f base extras copies hc theta
      · exact OrdinarySubstitutionStabilitySupportProof.successfulOriginalApply Symbol arity _ _ _ _ types q copies suffix r theta ha
      · exact ih Δ theta
  case mark s r t hm hw ih Δ theta =>
      apply SourceExtendedComparison.Strict.mark (substituteTerm s theta) (substituteTerm r theta) (substituteTerm t theta)
      · exact SuccessfulApplicationPostProof.strictMarkSubstitution Symbol arity _ _ _ s r theta hm
      · exact ih Δ theta
  case nil => exact .nil
  case cons s t ss ts hw hm ihw ihm Δ theta =>
      exact .cons _ _ _ _ (ihw Δ theta) (ihm Δ theta)
  case replace ss ts kept retained removed inserted hp hq hn hw hr ihw ihr Δ theta =>
      apply SourceExtendedComparison.StrictMultiset.replace _ _ (kept.map (substitutePacked theta)) (retained.map (substitutePacked theta))
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

theorem strictCovariance : ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop) (Γ Δ : List Ty) (theta : MarkedSubstitution Symbol arity Γ Δ) (s t : Packed Symbol arity Γ), SourceExtendedComparison.Strict Symbol arity above Γ s t → SourceExtendedComparison.Strict Symbol arity above Δ (substitutePacked theta s) (substitutePacked theta t) := by
  intro Symbol arity above Γ Δ theta s t h
  cases h with
  | mark s r t hm hw =>
      apply SourceExtendedComparison.Strict.mark (substituteTerm s theta) (substituteTerm r theta) (substituteTerm t theta)
      · exact SuccessfulApplicationPostProof.strictMarkSubstitution Symbol arity _ _ _ s r theta hm
      · exact weakCovariance Symbol arity above Γ Δ theta _ _ hw

theorem weakMatchCovariance : ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop) (Γ Δ : List Ty) (theta : MarkedSubstitution Symbol arity Γ Δ) (ss ts : List (Packed Symbol arity Γ)), SourceExtendedComparison.WeakMatch Symbol arity above Γ ss ts → SourceExtendedComparison.WeakMatch Symbol arity above Δ (ss.map (substitutePacked theta)) (ts.map (substitutePacked theta)) := by
  intro Symbol arity above Γ Δ theta ss
  induction ss with
  | nil => intro ts h; cases h; exact .nil
  | cons s ss ih =>
      intro ts h
      cases h with
      | cons _ t _ ts hw hm => exact .cons _ _ _ _ (weakCovariance Symbol arity above Γ Δ theta _ _ hw) (ih ts hm)

theorem replacementMatchCovariance : ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop) (Γ Δ : List Ty) (theta : MarkedSubstitution Symbol arity Γ Δ) (ss ts : List (Packed Symbol arity Γ)), SourceExtendedComparison.ReplacementMatch Symbol arity above Γ ss ts → SourceExtendedComparison.ReplacementMatch Symbol arity above Δ (ss.map (substitutePacked theta)) (ts.map (substitutePacked theta)) := by
  intro Symbol arity above Γ Δ theta ss ts
  induction ts with
  | nil => intro h; exact .nil _
  | cons t ts ih =>
      intro h
      cases h with
      | cons _ s _ _ hs hst hr =>
          exact .cons _ _ _ _ (List.mem_map.mpr ⟨s,hs,rfl⟩) (strictCovariance Symbol arity above Γ Δ theta _ _ hst) (ih hr)

theorem strictMultisetCovariance : ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop) (Γ Δ : List Ty) (theta : MarkedSubstitution Symbol arity Γ Δ) (ss ts : List (Packed Symbol arity Γ)), SourceExtendedComparison.StrictMultiset Symbol arity above Γ ss ts → SourceExtendedComparison.StrictMultiset Symbol arity above Δ (ss.map (substitutePacked theta)) (ts.map (substitutePacked theta)) := by
  intro Symbol arity above Γ Δ theta ss ts h
  cases h with
  | replace _ _ kept retained removed inserted hp hq hn hw hr =>
      apply SourceExtendedComparison.StrictMultiset.replace _ _ (kept.map (substitutePacked theta)) (retained.map (substitutePacked theta))
        (removed.map (substitutePacked theta)) (inserted.map (substitutePacked theta))
      · simpa only [List.map_append] using hp.map (substitutePacked theta)
      · simpa only [List.map_append] using hq.map (substitutePacked theta)
      · intro he
        exact hn (List.map_eq_nil_iff.mp he)
      · exact weakMatchCovariance Symbol arity above Γ Δ theta _ _ hw
      · exact replacementMatchCovariance Symbol arity above Γ Δ theta _ _ hr

theorem actualJointCovariance : SourceExtendedSubstitutionTargets.ActualJointCovariance := by
  intro Symbol arity above
  exact ⟨fun Γ s t h Δ theta => weakCovariance Symbol arity above Γ Δ theta s t h,
    fun Γ s t h Δ theta => strictCovariance Symbol arity above Γ Δ theta s t h,
    fun Γ ss ts h Δ theta => weakMatchCovariance Symbol arity above Γ Δ theta ss ts h,
    fun Γ ss ts h Δ theta => strictMultisetCovariance Symbol arity above Γ Δ theta ss ts h,
    fun Γ ss ts h Δ theta => replacementMatchCovariance Symbol arity above Γ Δ theta ss ts h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedSubstitutionProof
