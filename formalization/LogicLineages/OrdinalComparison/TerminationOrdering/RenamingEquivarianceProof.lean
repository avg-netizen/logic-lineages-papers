module
public import LogicLineages.OrdinalComparison.TerminationOrdering.RenamingEquivarianceApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.LiteralContextsProof
public import LogicLineages.OrdinalComparison.SourceTypeSupportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.RenamingEquivarianceProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication Source.SourceTypeSupport
open RecursiveComparison LiteralContexts RenamingEquivariance RenamingEquivarianceBindingProof

theorem substitutionCovariance : RenamingEquivarianceTargets.SubstitutionCovariance := RenamingEquivarianceBindingProof.substitutionCovariance
theorem originalApplyCovariance : RenamingEquivarianceTargets.OriginalApplyCovariance := RenamingEquivarianceApplicationProof.originalApplyCovariance

theorem argumentListRename {Symbol : Type} {arity : Symbol → Nat} {Γ Δ types : List Ty}
    (args : Arguments Symbol arity Γ types) (ρ : Renaming Γ Δ) :
    argumentList (renameArguments args ρ)=(argumentList args).map (renamePacked ρ) := by
  induction types with
  | nil => cases args; rfl
  | cons σ types ih => cases args with
    | cons q rest => exact congrArg (List.cons (renamePacked ρ ⟨σ,q⟩)) (ih rest)

theorem renameSelfArguments {Symbol : Type} {arity : Symbol → Nat} {Γ Δ : List Ty}
    (f : Head Symbol) (base : Arguments Symbol arity Γ (headArguments arity f))
    (extrasTypes : List Ty) (extras : Arguments Symbol arity Γ extrasTypes) (types : List Ty) (ρ : Renaming Γ Δ) :
    renameArguments (selfArguments f base extrasTypes extras types) ρ=
      selfArguments f (renameArguments base ρ) extrasTypes (renameArguments extras ρ) types := by
  induction types with
  | nil => rfl
  | cons σ types ih => exact congrArg (Arguments.cons (.marked f σ (renameArguments base ρ) extrasTypes (renameArguments extras ρ))) ih

theorem renameStrictMark {Symbol : Type} {arity : Symbol → Nat} {Γ Δ : List Ty} {τ : Ty}
    (q : MarkedTerm Symbol arity Γ τ) (ρ : Renaming Γ Δ) :
    strictMark (renameTerm q ρ)=(strictMark q).map (fun r => renameTerm r ρ) := by
  induction q using MarkedTerm.rec (motive_2 := fun _ _ _ => True) generalizing Δ with
  | var v => rfl
  | lam body ih =>
      simp only [renameTerm,strictMark,ih,Option.map_map]
      rfl
  | ordinary hd args ih => rfl
  | marked hd out args types extras iha ihe => rfl
  | nil => trivial
  | cons q rest ihq ihr => trivial

theorem renameOpen {Symbol : Type} {arity : Symbol → Nat} {Γ Δ : List Ty}
    (f : Head Symbol) (σ τ : Ty) (base : Arguments Symbol arity Γ (headArguments arity f))
    (types : List Ty) (extras : Arguments Symbol arity Γ types) (ρ : Renaming Γ Δ) :
    renameTerm (openMarked f σ τ base types extras) ρ.lift=
      openMarked f σ τ (renameArguments base ρ) types (renameArguments extras ρ) := by
  simp only [openMarked,renameTerm,renameAppend,renameArgumentsComposition,renameArguments,Renaming.lift]
  rfl

theorem weakCovariance : RenamingEquivarianceTargets.WeakCovariance := by
  intro Symbol arity above Γ Δ ρ s t h
  induction h using Weak.rec
    (motive_2 := fun Γ s t _ => ∀ (Δ : List Ty) (ρ : Renaming Γ Δ), Strict Symbol arity above Δ (renamePacked ρ s) (renamePacked ρ t))
    (motive_3 := fun Γ ss ts _ => ∀ (Δ : List Ty) (ρ : Renaming Γ Δ), WeakMatch Symbol arity above Δ (ss.map (renamePacked ρ)) (ts.map (renamePacked ρ)))
    (motive_4 := fun Γ ss ts _ => ∀ (Δ : List Ty) (ρ : Renaming Γ Δ), StrictMultiset Symbol arity above Δ (ss.map (renamePacked ρ)) (ts.map (renamePacked ρ)))
    (motive_5 := fun Γ ss ts _ => ∀ (Δ : List Ty) (ρ : Renaming Γ Δ), ReplacementMatch Symbol arity above Δ (ss.map (renamePacked ρ)) (ts.map (renamePacked ρ)))
    generalizing Δ
  case var v => exact .var (ρ v)
  case abs s t hw ih => exact .abs _ _ (ih _ ρ.lift)
  case fun_ f g ss ts matched he ht hp hm ih =>
      apply Weak.fun_ f g (renameArguments ss ρ) (renameArguments ts ρ) (matched.map (renamePacked ρ)) he ht
      · rw [argumentListRename]; exact hp.map _
      · rw [argumentListRename]; exact ih Δ ρ
  case put f ss t hw ih => exact .put f (renameArguments ss ρ) (renameTerm t ρ) (ih Δ ρ)
  case select f ss extraTypes extras types q r t suffix hmem happ hw ih =>
      apply Weak.select f (renameArguments ss ρ) extraTypes (renameArguments extras ρ) types
        (renameTerm q ρ) (renameTerm r ρ) (renameTerm t ρ) suffix
      · rw [argumentListRename,argumentListRename,←List.map_append]
        exact List.mem_map.mpr ⟨_,hmem,rfl⟩
      · rw [←renameSelfArguments]
        have hc := originalApplyCovariance Symbol arity _ _ _ _ _ _ types q
          (selfArguments f ss extraTypes extras types) ρ ρ (fun v => .var v) (fun v => .var v) suffix (by intros; rfl)
        exact hc.trans (by rw [happ]; rfl)
      · exact ih Δ ρ
  case fAbs f ss extraTypes extras t hw ih =>
      apply Weak.fAbs f (renameArguments ss ρ) extraTypes (renameArguments extras ρ) (renameTerm t ρ.lift)
      have hc := ih _ ρ.lift
      simpa only [renamePacked,renameOpen] using hc
  case copy f g ss extraTypes extras ts ha hw ih =>
      apply Weak.copy f g (renameArguments ss ρ) extraTypes (renameArguments extras ρ) (renameArguments ts ρ) ha
      intro p hp
      rw [argumentListRename] at hp
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
      exact ih q hq Δ ρ
  case stat f g ss extraTypes extras ts he hm hw ihm ihw =>
      apply Weak.stat f g (renameArguments ss ρ) extraTypes (renameArguments extras ρ) (renameArguments ts ρ) he
      · rw [argumentListRename,argumentListRename]; exact ihm Δ ρ
      · intro p hp
        rw [argumentListRename] at hp
        obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
        exact ihw q hq Δ ρ
  case mark s r t hm hw ih Δ ρ =>
      apply Strict.mark (renameTerm s ρ) (renameTerm r ρ) (renameTerm t ρ)
      · rw [renameStrictMark,hm]; rfl
      · exact ih Δ ρ
  case nil => exact .nil
  case cons s t ss ts hw hm ihw ihm Δ ρ =>
      exact .cons _ _ _ _ (ihw Δ ρ) (ihm Δ ρ)
  case replace ss ts kept retained removed inserted hp hq hn hw hr ihw ihr Δ ρ =>
      apply StrictMultiset.replace _ _ (kept.map (renamePacked ρ)) (retained.map (renamePacked ρ))
        (removed.map (renamePacked ρ)) (inserted.map (renamePacked ρ))
      · simpa only [List.map_append] using hp.map (renamePacked ρ)
      · simpa only [List.map_append] using hq.map (renamePacked ρ)
      · intro he
        exact hn (List.map_eq_nil_iff.mp he)
      · exact ihw Δ ρ
      · exact ihr Δ ρ
  case nil removed Δ =>
      intro ρ
      exact .nil _
  case cons removed s t rest hs hst hr ihst ihr Δ =>
      intro ρ
      exact .cons _ _ _ _ (List.mem_map.mpr ⟨s,hs,rfl⟩) (ihst Δ ρ) (ihr Δ ρ)

theorem strictCovariance : RenamingEquivarianceTargets.StrictCovariance := by
  intro Symbol arity above Γ Δ ρ s t h
  cases h with
  | mark s r t hm hw =>
      apply Strict.mark (renameTerm s ρ) (renameTerm r ρ) (renameTerm t ρ)
      · rw [renameStrictMark,hm]; rfl
      · exact weakCovariance Symbol arity above Γ Δ ρ _ _ hw

theorem weakMatchCovariance : RenamingEquivarianceTargets.WeakMatchCovariance := by
  intro Symbol arity above Γ Δ ρ ss
  induction ss with
  | nil => intro ts h; cases h; exact .nil
  | cons s ss ih =>
      intro ts h
      cases h with
      | cons _ t _ ts hw hm => exact .cons _ _ _ _ (weakCovariance Symbol arity above Γ Δ ρ _ _ hw) (ih ts hm)

theorem replacementMatchCovariance : RenamingEquivarianceTargets.ReplacementMatchCovariance := by
  intro Symbol arity above Γ Δ ρ ss ts
  induction ts with
  | nil => intro h; exact .nil _
  | cons t ts ih =>
      intro h
      cases h with
      | cons _ s _ _ hs hst hr =>
          exact .cons _ _ _ _ (List.mem_map.mpr ⟨s,hs,rfl⟩) (strictCovariance Symbol arity above Γ Δ ρ _ _ hst) (ih hr)

theorem strictMultisetCovariance : RenamingEquivarianceTargets.StrictMultisetCovariance := by
  intro Symbol arity above Γ Δ ρ ss ts h
  cases h with
  | replace _ _ kept retained removed inserted hp hq hn hw hr =>
      apply StrictMultiset.replace _ _ (kept.map (renamePacked ρ)) (retained.map (renamePacked ρ))
        (removed.map (renamePacked ρ)) (inserted.map (renamePacked ρ))
      · simpa only [List.map_append] using hp.map (renamePacked ρ)
      · simpa only [List.map_append] using hq.map (renamePacked ρ)
      · intro he
        exact hn (List.map_eq_nil_iff.mp he)
      · exact weakMatchCovariance Symbol arity above Γ Δ ρ _ _ hw
      · exact replacementMatchCovariance Symbol arity above Γ Δ ρ _ _ hr

theorem renamedContextStrictClosure : RenamingEquivarianceTargets.RenamedContextStrictClosure := by
  intro Symbol arity above Ξ Δ Γ υ τ ρ C s t h
  apply LiteralContextsProof.literalContextStrictClosure Symbol arity above Δ Γ υ τ C
  have hr := strictCovariance Symbol arity above Ξ Δ ρ _ _ h
  rw [Source.SourceMarkedBindingProof.embeddingRenaming Symbol arity Ξ Δ υ s ρ,
    Source.SourceMarkedBindingProof.embeddingRenaming Symbol arity Ξ Δ υ t ρ]
  exact hr

theorem renamedConfinedContextClosure : RenamingEquivarianceTargets.RenamedConfinedContextClosure := by
  intro Symbol arity above Ξ Δ Γ υ τ ρ C s t h
  refine ⟨renamedContextStrictClosure Symbol arity above Ξ Δ Γ υ τ ρ C s t h.1,?_⟩
  apply LiteralContextsProof.literalContextSupportMonotonicity Symbol arity Δ Γ υ τ C
  rw [(Source.SourceTypeSupportProof.supportDepthRenaming Symbol arity Ξ Δ υ t ρ).1,
    (Source.SourceTypeSupportProof.supportDepthRenaming Symbol arity Ξ Δ υ s ρ).1]
  exact h.2

end LogicLineages.OrdinalComparison.TerminationOrdering.RenamingEquivarianceProof
