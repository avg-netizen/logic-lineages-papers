module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceGroundContextTowerTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceGroundContextTowerProof
open Source NumberedRewriteSyntax NumberedFiniteUniverse NumberedLeastCodeRepresentative SourceGroundContextTower

theorem renameFixed {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {tau : Ty}
    (q : AuxTerm Symbol arity Gamma tau) : ∀ rho : Renaming Gamma Gamma,
    (∀ (upsilon : Ty) (v : Variable Gamma upsilon), rho v = v) → rename q rho = q := by
  induction q using AuxTerm.rec
    (motive_2 := fun Gamma types args => ∀ rho : Renaming Gamma Gamma,
      (∀ (upsilon : Ty) (v : Variable Gamma upsilon), rho v = v) → renameArguments args rho = args)
  case var v => intro rho h; exact congrArg AuxTerm.var (h _ v)
  case lam body ih =>
    intro rho h
    apply congrArg AuxTerm.lam
    apply ih rho.lift
    intro upsilon v
    cases v with
    | here => rfl
    | there v => exact congrArg Variable.there (h _ v)
  case app f a ihf iha => intro rho h; exact congrArg₂ AuxTerm.app (ihf rho h) (iha rho h)
  case bottom => intros; rfl
  case ordinary f base ih => intro rho h; exact congrArg (AuxTerm.ordinary f) (ih rho h)
  case numbered k f tau base types extras ihb ihe =>
    intro rho h
    exact congrArg₂ (fun b e => AuxTerm.numbered k f tau b types e) (ihb rho h) (ihe rho h)
  case nil => intros; rfl
  case cons Gamma sigma types q rest ihq ihr rho h => exact congrArg₂ AuxArguments.cons (ihq rho h) (ihr rho h)

theorem actualGroundContextEquation : SourceGroundContextTowerTargets.ActualGroundContextEquation := by
  intro k Gamma
  induction k with
  | zero => rfl
  | succ k ih => simp only [groundContext,List.replicate_succ,List.cons_append,ih]

theorem actualGroundRenamingEquations : SourceGroundContextTowerTargets.ActualGroundRenamingEquations := by
  intro Symbol arity Gamma tau q
  refine ⟨renameFixed q _ (by intros; rfl),?_⟩
  intro k
  exact (NumberedRenamingCompositionProof.actualTermRenamingComposition Symbol arity Gamma
    (groundContext k Gamma) (groundContext (k + 1) Gamma)
    (groundRenaming k Gamma) (Renaming.weaken (groundContext k Gamma) .ground) tau q).symm

theorem actualGroundTowerComputability : SourceGroundContextTowerTargets.ActualGroundTowerComputability := by
  intro n arity Gamma context ctx k scalar hc hclosed
  induction k with
  | zero =>
    intro hcal q hq
    rw [(actualGroundRenamingEquations (Fin n) arity Gamma .ground q).1]
    rfl
  | succ k ih =>
    intro hcal q hq
    have hprev := ih (fun j hj => hcal j (Nat.le_trans hj (Nat.le_succ k))) q hq
    have hgood := NumberedUniverseBindingProof.actualRenaming (Fin n) arity
      (fun t => t ∈ ctx.1.2) (HeadInWindow arity ctx.1.1 ctx.1.2)
      Gamma (groundContext k Gamma) .ground q (groundRenaming k Gamma) hq
    have hnext := SourceGroundWeakeningProof.actualGroundComputabilityWeakening n arity
      (groundContext k Gamma) context ctx (scalar k) (scalar (k + 1)) hc hclosed .ground
      (hcal k (Nat.le_succ k)) (hcal (k + 1) (Nat.le_refl _))
      (rename q (groundRenaming k Gamma)) hgood
    rw [(actualGroundRenamingEquations (Fin n) arity Gamma .ground q).2 k]
    exact hprev.trans hnext

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceGroundContextTowerProof
