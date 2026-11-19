import LogicLineages.PersistentMarking.NumberedWindowClosingOperationsProof
import LogicLineages.PersistentMarking.NumberedWindowClosingTypedProof

namespace LogicLineages.PersistentMarking.NumberedWindowClosingPrimaryProof
open NumberedWindowSyntax NumberedWindowPrimary NumberedWindowClosing
open NumberedWindowClosingOperationsProof (asList)
open NumberedWindowClosingTypedProof (base extras push)
open NameBridge (Name)

private theorem perm (n : Name) (d : Nat) {bs cs}
    (h : bs.toList.Perm cs.toList) :
    (closeArgsAt n d bs).toList.Perm (closeArgsAt n d cs).toList := by
  simpa only [asList] using h.map (closeAt n d)

theorem term (n : Name) {S K C τ q r} (h : Primary S K C τ q r) :
    ∀ d D, CloseCompatible n d C D →
      Primary S K D τ (closeAt n d q) (closeAt n d r) := by
  induction h using Primary.rec (motive_2 := fun C types qs rs _ =>
    ∀ d D, CloseCompatible n d C D →
      OrderedPrimary S K D types (closeArgsAt n d qs) (closeArgsAt n d rs)) with
  | refl ht =>
    intro d D hc
    exact .refl (NumberedWindowClosingTypedProof.term n d _ D _ _ ht hc)
  | symm _ ih => intro d D hc; exact .symm (ih d D hc)
  | trans _ _ iq ir => intro d D hc; exact .trans (iq d D hc) (ir d D hc)
  | ordinary hf hg he ht hb hc hp =>
    intro d D hEnv
    exact .ordinary hf hg he ht (base n d _ D _ _ hb hEnv) (base n d _ D _ _ hc hEnv) (perm n d hp)
  | numbered hf hg he hb hc hs hp =>
    intro d D hEnv
    exact .numbered hf hg he (base n d _ D _ _ hb hEnv) (base n d _ D _ _ hc hEnv)
      (extras n d _ D _ hs hEnv) (perm n d hp)
  | lam _ ih =>
    intro d D hc
    exact .lam (ih (d+1) _ (push hc _))
  | appFunction _ ha ih =>
    intro d D hc
    exact .appFunction (ih d D hc) (NumberedWindowClosingTypedProof.term n d _ D _ _ ha hc)
  | appArgument hq _ ih =>
    intro d D hc
    exact .appArgument (NumberedWindowClosingTypedProof.term n d _ D _ _ hq hc) (ih d D hc)
  | ordinaryArguments _ ih =>
    intro d D hc
    exact .ordinaryArguments (ih d D hc)
  | numberedBase _ he ih =>
    intro d D hc
    exact .numberedBase (ih d D hc) (extras n d _ D _ he hc)
  | numberedExtras hb _ ih =>
    intro d D hc
    exact .numberedExtras (base n d _ D _ _ hb hc) (ih d D hc)
  | nil => intros; exact .nil
  | cons _ _ iq ir => intro d D hc; exact .cons (iq d D hc) (ir d D hc)

end LogicLineages.PersistentMarking.NumberedWindowClosingPrimaryProof
