module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRewriteApplicationDefinitions

@[expose] public section
/-! Exact source06 application dynamics for the existing typed numbered raw
reduction. Its auxiliary application reduces only in its function position,
by beta at a lambda function, or to same-type bottom. The original functional
application head remains a distinct ordinary head.

The finite-path statement identifies the first root beta contraction when one
occurs. The accessibility statement retains every beta contractum reachable
through the actual original function relation. No argument reduction,
substitution compatibility, finite-window restriction or normalization oracle
is added. These are native supporting statements for the lambda/application
argument of `lem:id1`, not internal certificate or quotient accessibility.
-/
namespace LogicLineages.OrdinalComparison.TerminationOrdering.Continuation20261117.RawApplicationDynamics.Targets
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedRewriteApplication

/-- A finite raw application path either ends in bottom, retains the same
argument while reducing its function, or passes through a genuine reachable
lambda and continues from that lambda's literal beta contractum. -/
def ActualRawApplicationPathFactorization : Prop :=
  ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
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
          (substitute body (singleSubstitution a)) target

/-- Exact raw application accessibility: the function is accessible, and
every beta contractum reached through a finite function path is accessible.
The argument is kept fixed, as required by the original raw relation. -/
def ActualRawApplicationAccessibilityEquivalence : Prop :=
  ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
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
        (substitute body (singleSubstitution a))

end LogicLineages.OrdinalComparison.TerminationOrdering.Continuation20261117.RawApplicationDynamics.Targets
