module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceGroundLambdaTowerTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceGroundLambdaTowerSupportProof
open Source NumberedRewriteSyntax SourceGroundContextTower SourceGroundContextTowerProof

theorem contextShift (j : Nat) (Gamma : List Ty) :
    groundContext j (.ground :: Gamma) = groundContext (j + 1) Gamma := by
  induction j with
  | zero => rfl
  | succ j ih => exact congrArg (List.cons Ty.ground) ih

/-- A literal dependent-context renaming equation, expressed for an arbitrary property. -/
theorem shiftedRenamingProperty {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {tau : Ty}
    (q : AuxTerm Symbol arity Gamma tau) (j : Nat)
    (F : ∀ Delta : List Ty, AuxTerm Symbol arity Delta tau → Prop) :
    F (groundContext j (.ground :: Gamma))
      (rename (rename q (Renaming.weaken Gamma .ground)) (groundRenaming j (.ground :: Gamma))) ↔
    F (groundContext (j + 1) Gamma) (rename q (groundRenaming (j + 1) Gamma)) := by
  induction j generalizing F with
  | zero =>
    rw [(actualGroundRenamingEquations Symbol arity (.ground :: Gamma) tau
      (rename q (Renaming.weaken Gamma .ground))).1,
      (actualGroundRenamingEquations Symbol arity Gamma tau q).2 0,
      (actualGroundRenamingEquations Symbol arity Gamma tau q).1]
    rfl
  | succ j ih =>
    rw [(actualGroundRenamingEquations Symbol arity (.ground :: Gamma) tau
      (rename q (Renaming.weaken Gamma .ground))).2 j,
      (actualGroundRenamingEquations Symbol arity Gamma tau q).2 (j + 1)]
    exact ih (fun Delta r => F (.ground :: Delta) (rename r (Renaming.weaken Delta .ground)))

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceGroundLambdaTowerSupportProof
