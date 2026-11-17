module
public import LogicLineages.OrdinalComparison.TerminationOrdering.Continuation20261117.RawLambdaDynamics.Targets
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.Continuation20261117.RawLambdaDynamics.ComparatorGate
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedRewriteApplication

theorem exactRawLambdaPathFactorization : Targets.ActualRawLambdaPathFactorization ↔
    (∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
      (Gamma : List Ty) (sigma tau : Ty)
      (body : AuxTerm Symbol arity (sigma :: Gamma) tau)
      (target : AuxTerm Symbol arity Gamma (.arrow sigma tau)),
    RawSteps Symbol arity above Gamma (.arrow sigma tau) (.lam body) target ↔
      target = .bottom (.arrow sigma tau) ∨
        ∃ next : AuxTerm Symbol arity (sigma :: Gamma) tau,
          RawSteps Symbol arity above (sigma :: Gamma) tau body next ∧
          target = .lam next) := Iff.rfl

theorem exactRawLambdaAccessibilityEquivalence :
    Targets.ActualRawLambdaAccessibilityEquivalence ↔
    (∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
      (Gamma : List Ty) (sigma tau : Ty)
      (body : AuxTerm Symbol arity (sigma :: Gamma) tau),
    Acc (fun successor source =>
      RawStep Symbol arity above Gamma (.arrow sigma tau) source successor)
        (.lam body) ↔
    Acc (fun successor source =>
      RawStep Symbol arity above (sigma :: Gamma) tau source successor) body) := Iff.rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.Continuation20261117.RawLambdaDynamics.ComparatorGate
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.Continuation20261117.RawLambdaDynamics.ComparatorGate
