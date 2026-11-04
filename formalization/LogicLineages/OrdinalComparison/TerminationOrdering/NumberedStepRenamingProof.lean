module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedStepRenamingTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedStepRenamingProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedWindowReduction NumberedPrimarySubstitution
open NumberedArgumentSubstitutionProof NumberedPrimarySubstitutionProof NumberedPrimaryWeakeningProof

def NonBottomImages {Symbol : Type} {arity : Symbol → Nat} {Gamma Delta : List Ty}
    (theta : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta) : Prop :=
  ∀ {tau : Ty} (v : Variable Gamma tau), theta v ≠ .bottom tau

theorem renameNonBottom {Symbol : Type} {arity : Symbol → Nat} {Gamma Delta : List Ty} {tau : Ty}
    (q : AuxTerm Symbol arity Gamma tau) (rho : Renaming Gamma Delta) (h : q ≠ .bottom tau) :
    NumberedRewriteSyntax.rename q rho ≠ .bottom tau := by
  cases q <;> simp_all [NumberedRewriteSyntax.rename]

theorem liftNonBottom {Symbol : Type} {arity : Symbol → Nat} {Gamma Delta : List Ty} {sigma : Ty}
    (theta : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta) (h : NonBottomImages theta) :
    NonBottomImages (liftSubstitution (sigma := sigma) theta) := by
  intro tau v
  cases v with
  | here => intro he; cases he
  | there v => exact renameNonBottom (theta v) (Renaming.weaken Delta sigma) (h v)

theorem substituteNonBottom {Symbol : Type} {arity : Symbol → Nat} {Gamma Delta : List Ty} {tau : Ty}
    (q : AuxTerm Symbol arity Gamma tau) (theta : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta)
    (h : q ≠ .bottom tau) (hn : NonBottomImages theta) : substitute q theta ≠ .bottom tau := by
  cases q with
  | var v => exact hn v
  | bottom => exact False.elim (h rfl)
  | lam body => intro he; cases he
  | app f a => intro he; cases he
  | ordinary f base => intro he; cases he
  | numbered k f tau base types extras => intro he; cases he

theorem substituteStrictStep {Symbol : Type} {arity : Symbol → Nat} {symbols : List Symbol} {S : List Ty}
    {above : Symbol → Symbol → Prop} {Gamma : List Ty} {tau : Ty} {q r : AuxTerm Symbol arity Gamma tau}
    (h : WindowStep Symbol arity symbols S above Gamma tau q r) :
    ∀ (Delta : List Ty) (theta : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta), NonBottomImages theta →
    WindowStep Symbol arity symbols S above Delta tau (substitute q theta) (substitute r theta) := by
  induction h using WindowStep.rec
    (motive_2 := fun Gamma types base target _ => ∀ (Delta : List Ty)
      (theta : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta), NonBottomImages theta →
      WindowArgumentStep Symbol arity symbols S above Delta types
        (substituteArguments base theta) (substituteArguments target theta))
  case put label f base => intro Delta theta hn; exact .put label f _
  case select label f base types extras ts selected hm =>
    intro Delta theta hn
    simp only [substitute]
    rw [actualApplyArgumentsSubstitution,actualSelfArgumentsSubstitution]
    apply WindowStep.select label f _ types _ ts (substitute selected theta)
    rw [argumentListSubstitute,argumentListSubstitute,← List.map_append]
    exact List.mem_map.mpr ⟨_,hm,rfl⟩
  case copy label f g base types extras hg hw =>
    intro Delta theta hn
    simp only [substitute]
    rw [actualSelfArgumentsSubstitution]
    exact .copy label f g _ types _ hg hw
  case mul label f g base types extras target hg hm hw =>
    intro Delta theta hn
    apply WindowStep.mul label f g _ types _ _ hg _ hw
    rw [argumentListSubstitute,argumentListSubstitute]
    exact NumberedMarkSubstitutionProof.actualPrimitiveMultisetSubstitution Symbol arity _ Delta theta _ _ hm
  case abs label f base types extras =>
    intro Delta theta hn
    simp only [substitute]
    rw [NumberedOpeningSubstitutionProof.actualOpenNumberedSubstitution]
    exact .abs label f _ types _
  case ordinaryArguments f base target h ih =>
    intro Delta theta hn
    exact .ordinaryArguments f _ _ (ih Delta theta hn)
  case numberedBase label f tau base target types extras h ih =>
    intro Delta theta hn
    exact .numberedBase label f tau _ _ types _ (ih Delta theta hn)
  case numberedExtras label f tau base types extras target h ih =>
    intro Delta theta hn
    exact .numberedExtras label f tau _ types _ _ (ih Delta theta hn)
  case appFunction q r a h ih =>
    intro Delta theta hn
    exact .appFunction _ _ _ (ih Delta theta hn)
  case lam q r h ih =>
    intro Delta theta hn
    exact .lam _ _ (ih _ (liftSubstitution theta) (liftNonBottom theta hn))
  case beta body a =>
    intro Delta theta hn
    rw [NumberedSubstitutionCompositionProof.actualBetaSubstitution]
    exact .beta _ _
  case bottom q hq =>
    intro Delta theta hn
    exact .bottom _ (substituteNonBottom q theta hq hn)
  case head Gamma sigma types q r rest h ih Delta theta hn =>
    exact .head _ _ _ (ih Delta theta hn)
  case tail Gamma sigma types q rest target h ih Delta theta hn =>
    exact .tail _ _ _ (ih Delta theta hn)

theorem actualStepRenaming : NumberedStepRenamingTargets.ActualStepRenaming := by
  intro Symbol arity symbols S above Gamma Delta rho tau q r h
  rw [actualTermRenameAsSubstitution,actualTermRenameAsSubstitution]
  exact substituteStrictStep h Delta (fun v => .var (rho v)) (by intro tau v he; cases he)

theorem actualArgumentStepRenaming : NumberedStepRenamingTargets.ActualArgumentStepRenaming := by
  intro Symbol arity symbols S above Gamma Delta rho types base target h
  induction types with
  | nil => cases h
  | cons sigma types ih => cases h with
    | head q r rest hs => exact .head _ _ _ (actualStepRenaming Symbol arity symbols S above Gamma Delta rho sigma q r hs)
    | tail q rest target hs => exact .tail _ _ _ (ih rest target hs)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedStepRenamingProof
