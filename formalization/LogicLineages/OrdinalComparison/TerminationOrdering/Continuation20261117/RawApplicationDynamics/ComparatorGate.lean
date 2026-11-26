module
public import LogicLineages.OrdinalComparison.TerminationOrdering.Continuation20261117.RawApplicationDynamics.Targets
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.Continuation20261117.RawApplicationDynamics.ComparatorGate
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedRewriteApplication

theorem exactRawApplicationPathFactorization :
    Targets.ActualRawApplicationPathFactorization ↔
    (∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
      (Gamma : List Ty) (sigma tau : Ty)
      (f : AuxTerm Symbol arity Gamma (.arrow sigma tau))
      (a : AuxTerm Symbol arity Gamma sigma)
      (target : AuxTerm Symbol arity Gamma tau),
    RawSteps Symbol arity above Gamma tau (.app f a) target ↔
      target = .bottom tau ∨
        (∃ next : AuxTerm Symbol arity Gamma (.arrow sigma tau),
          RawSteps Symbol arity above Gamma (.arrow sigma tau) f next ∧
          target = .app next a) ∨
        ∃ body : AuxTerm Symbol arity (sigma :: Gamma) tau,
          RawSteps Symbol arity above Gamma (.arrow sigma tau) f (.lam body) ∧
          RawSteps Symbol arity above Gamma tau
            (substitute body (singleSubstitution a)) target) := Iff.rfl

theorem exactRawApplicationAccessibilityEquivalence :
    Targets.ActualRawApplicationAccessibilityEquivalence ↔
    (∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
      (Gamma : List Ty) (sigma tau : Ty)
      (f : AuxTerm Symbol arity Gamma (.arrow sigma tau))
      (a : AuxTerm Symbol arity Gamma sigma),
    Acc (fun successor source =>
      RawStep Symbol arity above Gamma tau source successor) (.app f a) ↔
      Acc (fun successor source =>
        RawStep Symbol arity above Gamma (.arrow sigma tau) source successor) f ∧
      ∀ body : AuxTerm Symbol arity (sigma :: Gamma) tau,
        RawSteps Symbol arity above Gamma (.arrow sigma tau) f (.lam body) →
        Acc (fun successor source =>
          RawStep Symbol arity above Gamma tau source successor)
          (substitute body (singleSubstitution a))) := Iff.rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.Continuation20261117.RawApplicationDynamics.ComparatorGate
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.Continuation20261117.RawApplicationDynamics.ComparatorGate
