module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimarySupportTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimarySupportProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedWindowEquivalence NumberedRenamingSupport

theorem actualArgumentSupportList : NumberedPrimarySupportTargets.ActualArgumentSupportList := by
  intro Symbol arity Gamma types P args
  induction types with
  | nil => cases args; simp [supportsArguments,argumentList]
  | cons tau types ih => cases args with
    | cons q rest => simp [supportsArguments,argumentList,ih]

theorem permSupport {Symbol : Type} {arity : Symbol → Nat} {Gamma xs ys : List Ty}
    (P : VariablePredicate Gamma) (base : AuxArguments Symbol arity Gamma xs)
    (target : AuxArguments Symbol arity Gamma ys) (h : (argumentList base).Perm (argumentList target)) :
    supportsArguments P base ↔ supportsArguments P target := by
  rw [actualArgumentSupportList,actualArgumentSupportList]
  exact ⟨fun hb q hq => hb q (h.mem_iff.mpr hq),fun ht q hq => ht q (h.mem_iff.mp hq)⟩

theorem primarySupport {Symbol : Type} {arity : Symbol → Nat} {symbols : List Symbol} {S Gamma : List Ty}
    {q r : Packed Symbol arity Gamma} (h : WindowPrimary Symbol arity symbols S Gamma q r) :
    ∀ P : VariablePredicate Gamma, supports P q.2 ↔ supports P r.2 := by
  induction h using WindowPrimary.rec
    (motive_2 := fun Gamma types base target _ => ∀ P : VariablePredicate Gamma,
      supportsArguments P base ↔ supportsArguments P target)
  case refl q => intro P; exact Iff.rfl
  case symm h ih => intro P; exact (ih P).symm
  case trans h1 h2 ih1 ih2 => intro P; exact (ih1 P).trans (ih2 P)
  case ordinary f g base target hf hg he ht hp => intro P; exact permSupport P base target hp
  case numbered k f g tau base target types extras hf hg he hp =>
    intro P
    exact and_congr (permSupport P base target hp) Iff.rfl
  case lam q r h ih => intro P; exact ih (liftPredicate P)
  case appFunction q r a h ih => intro P; exact and_congr (ih P) Iff.rfl
  case appArgument q a b h ih => intro P; exact and_congr Iff.rfl (ih P)
  case ordinaryArguments f base target h ih => intro P; exact ih P
  case numberedBase k f tau base target types extras h ih => intro P; exact and_congr (ih P) Iff.rfl
  case numberedExtras k f tau base types extras target h ih => intro P; exact and_congr Iff.rfl (ih P)
  case nil => intros; exact Iff.rfl
  case cons Gamma sigma types q r rest target hq ht ihq iht P => exact and_congr (ihq P) (iht P)

theorem actualPrimarySupport : NumberedPrimarySupportTargets.ActualPrimarySupport := by
  intro Symbol arity symbols S Gamma P q r h
  exact primarySupport h P

theorem actualArgumentPrimarySupport : NumberedPrimarySupportTargets.ActualArgumentPrimarySupport := by
  intro Symbol arity symbols S Gamma P types base target h
  induction types with
  | nil => cases h; exact Iff.rfl
  | cons tau types ih => cases h with
    | cons q r rest target hq ht => exact and_congr (primarySupport hq P) (ih rest target ht)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimarySupportProof
