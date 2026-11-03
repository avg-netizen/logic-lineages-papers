module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRewriteSyntaxTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRewriteSyntaxProof
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax

theorem canonicalNumbering : NumberedRewriteSyntaxTargets.ActualCanonicalNumbering := by
  intro Symbol arity n Gamma tau q
  induction q using MarkedTerm.rec
    (motive_2 := fun Gamma types args => ArgumentsRepresent Symbol arity n Gamma types args (canonicalArguments n args))
  case var v => exact .var v
  case lam body ih => exact .lam _ _ ih
  case ordinary f base ih => exact .ordinary f _ _ ih
  case marked f output base types extras ihb ihe => exact .numbered f output _ _ types _ _ n (Nat.le_refl _) ihb ihe
  case nil => exact .nil
  case cons q rest ihq ihr => exact .cons _ _ _ _ ihq ihr

theorem budgetLowering : NumberedRewriteSyntaxTargets.ActualBudgetLowering := by
  intro Symbol arity n m hmn Gamma tau q Q h
  induction h using Represents.rec
    (motive_2 := fun Gamma types args values _ => ArgumentsRepresent Symbol arity m Gamma types args values)
  case var v => exact .var v
  case lam q Q h ih => exact .lam _ _ ih
  case ordinary f base values h ih => exact .ordinary f _ _ ih
  case numbered f output base values types extras extraValues k hk hb he ihb ihe =>
    exact .numbered f output _ _ types _ _ k (Nat.le_trans hmn hk) ihb ihe
  case nil => exact .nil
  case cons q Q rest values hq hr ihq ihr => exact .cons _ _ _ _ ihq ihr

theorem groundCanonical {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (n m : Nat) (f : Fin m → Term Symbol arity Gamma .ground)
    (H : ∀ i,Represents Symbol arity n Gamma .ground (embed (f i)) (canonical 0 (embed (f i)))) :
    ArgumentsRepresent Symbol arity n Gamma (List.replicate m .ground)
      (groundArguments m (fun i => embed (f i)))
      (canonicalArguments 0 (groundArguments m (fun i => embed (f i)))) := by
  induction m with
  | zero => exact .nil
  | succ m ih => exact .cons _ _ _ _ (H 0) (ih (fun i => f i.succ) (fun i => H i.succ))

theorem ordinaryTranslation : NumberedRewriteSyntaxTargets.ActualOrdinaryTranslation := by
  intro Symbol arity n Gamma tau q
  induction q with
  | var v => exact .var v
  | app f a ihf iha => exact .ordinary (.application _ _) _ _ (.cons _ _ _ _ ihf (.cons _ _ _ _ iha .nil))
  | lam body ih => exact .lam _ _ ih
  | zeroC => exact .ordinary .zero .nil .nil .nil
  | succC => exact .ordinary .succ .nil .nil .nil
  | caseC tau => exact .ordinary (.cases tau) .nil .nil .nil
  | recC tau => exact .ordinary (.recursor tau) .nil .nil .nil
  | ranked f args ih => exact .ordinary (.ranked f) _ _ (groundCanonical n (arity f) args ih)

theorem renameRep {Symbol : Type} {arity : Symbol → Nat} {n : Nat} {Gamma : List Ty} {tau : Ty}
    {q : MarkedTerm Symbol arity Gamma tau} {Q : AuxTerm Symbol arity Gamma tau}
    (h : Represents Symbol arity n Gamma tau q Q) :
    ∀ (Delta : List Ty) (rho : Renaming Gamma Delta),
      Represents Symbol arity n Delta tau (Source.SourceMarkedBinding.renameTerm q rho) (NumberedRewriteSyntax.rename Q rho) := by
  induction h using Represents.rec
    (motive_2 := fun Gamma types args values _ => ∀ (Delta : List Ty) (rho : Renaming Gamma Delta),
      ArgumentsRepresent Symbol arity n Delta types
        (Source.SourceMarkedBinding.renameArguments args rho) (NumberedRewriteSyntax.renameArguments values rho))
  case var v => intro Delta rho; exact .var (rho v)
  case lam q Q h ih => intro Delta rho; exact .lam _ _ (ih _ rho.lift)
  case ordinary f base values h ih => intro Delta rho; exact .ordinary f _ _ (ih Delta rho)
  case numbered f output base values types extras extraValues k hk hb he ihb ihe =>
    intro Delta rho
    exact .numbered f output _ _ types _ _ k hk (ihb Delta rho) (ihe Delta rho)
  case nil => intros; exact .nil
  case cons rest values hq hr ihq ihr Delta rho =>
    exact .cons _ _ _ _ (ihq Delta rho) (ihr Delta rho)

theorem renamingCorrespondence : NumberedRewriteSyntaxTargets.ActualRenaming := by
  intro Symbol arity n Gamma Delta tau q Q rho h
  exact renameRep h Delta rho

theorem relatedSubstitution : NumberedRewriteSyntaxTargets.ActualRelatedSubstitution := by
  intro Symbol arity n Gamma Delta tau q Q rho sigma H h
  induction h using Represents.rec
    (motive_2 := fun Gamma types args values _ => ∀ (Delta : List Ty)
      (rho : Source.SourceMarkedBinding.MarkedSubstitution Symbol arity Gamma Delta)
      (sigma : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta),
      (∀ (upsilon : Ty) (v : Variable Gamma upsilon),Represents Symbol arity n Delta upsilon (rho v) (sigma v)) →
      ArgumentsRepresent Symbol arity n Delta types
        (Source.SourceMarkedBinding.substituteArguments args rho) (NumberedRewriteSyntax.substituteArguments values sigma))
    generalizing Delta
  case var v => exact H _ v
  case lam q Q h ih =>
    apply Represents.lam
    apply ih _ (Source.SourceMarkedBinding.liftSubstitution rho) (NumberedRewriteSyntax.liftSubstitution sigma)
    intro upsilon v
    cases v with
    | here => exact .var .here
    | there v => exact renameRep (H _ v) _ (Renaming.weaken Delta _)
  case ordinary f base values h ih => exact .ordinary f _ _ (ih Delta rho sigma H)
  case numbered f output base values types extras extraValues k hk hb he ihb ihe =>
    exact .numbered f output _ _ types _ _ k hk (ihb Delta rho sigma H) (ihe Delta rho sigma H)
  case nil => intros; exact .nil
  case cons q Q rest values hq hr ihq ihr Delta rho sigma H =>
    exact .cons _ _ _ _ (ihq Delta rho sigma H) (ihr Delta rho sigma H)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRewriteSyntaxProof
