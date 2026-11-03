module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedStepContextsTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedStepContextsProof
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedWindowReduction NumberedStepContexts

theorem liftTerm {n : Nat} {arity : Fin n → Nat} (symbols : List (Fin n)) (S : List Ty) (above : Fin n → Fin n → Prop)
    {holeGamma : List Ty} {holeType : Ty} (q r : AuxTerm (Fin n) arity holeGamma holeType)
    (h : WindowStep (Fin n) arity symbols S above holeGamma holeType q r)
    {Gamma : List Ty} {tau : Ty} (context : TermContext n arity holeGamma holeType Gamma tau) :
    WindowStep (Fin n) arity symbols S above Gamma tau (plug context q) (plug context r) := by
  induction context using TermContext.rec
    (motive_2 := fun Gamma types context => WindowArgumentStep (Fin n) arity symbols S above Gamma types (plugArguments context q) (plugArguments context r))
  case hole => exact h
  case lam body ih => exact .lam _ _ ih
  case appFunction fn arg ih => exact .appFunction _ _ arg ih
  case ordinary f base ih => exact .ordinaryArguments f _ _ ih
  case numberedBase label f tau base types extras ih => exact .numberedBase label f tau _ _ types extras ih
  case numberedExtras label f tau base types extras ih => exact .numberedExtras label f tau base types _ _ ih
  case head first rest ih => exact .head _ _ rest ih
  case tail first rest ih => exact .tail first _ _ ih

theorem liftArguments {n : Nat} {arity : Fin n → Nat} (symbols : List (Fin n)) (S : List Ty) (above : Fin n → Fin n → Prop)
    {holeGamma : List Ty} {holeType : Ty} (q r : AuxTerm (Fin n) arity holeGamma holeType)
    (h : WindowStep (Fin n) arity symbols S above holeGamma holeType q r)
    {Gamma types : List Ty} (context : ArgumentContext n arity holeGamma holeType Gamma types) :
    WindowArgumentStep (Fin n) arity symbols S above Gamma types (plugArguments context q) (plugArguments context r) := by
  induction context using ArgumentContext.rec
    (motive_1 := fun Gamma tau context => WindowStep (Fin n) arity symbols S above Gamma tau (plug context q) (plug context r))
  case hole => exact h
  case lam body ih => exact .lam _ _ ih
  case appFunction fn arg ih => exact .appFunction _ _ arg ih
  case ordinary f base ih => exact .ordinaryArguments f _ _ ih
  case numberedBase label f tau base types extras ih => exact .numberedBase label f tau _ _ types extras ih
  case numberedExtras label f tau base types extras ih => exact .numberedExtras label f tau base types _ _ ih
  case head first rest ih => exact .head _ _ rest ih
  case tail first rest ih => exact .tail first _ _ ih

theorem termContextStep : NumberedStepContextsTargets.ActualTermContextStep := by
  intro n arity symbols S above holeGamma holeType q r h Gamma tau context
  exact liftTerm symbols S above q r h context

theorem argumentContextStep : NumberedStepContextsTargets.ActualArgumentContextStep := by
  intro n arity symbols S above holeGamma holeType q r h Gamma types context
  exact liftArguments symbols S above q r h context

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedStepContextsProof
