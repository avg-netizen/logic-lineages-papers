module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRewriteApplicationDefinitions

@[expose] public section
/-! Lightweight source06 suppliers for the literal typed numbered auxiliary
reduction. The source lambda clause in `lem:id1` uses accessibility of the
lambda body; these statements isolate the corresponding native raw-reduction
facts without importing finite quotient codes or the internal ID1 pipeline.

Both relations below are the existing `RawStep` / `RawSteps`, with every
original constructor retained. No closure, precedence, source calibration,
normalization agreement or accessibility hypothesis is added. These are
supporting native statements, not internal derivations or a completion of the
source paper's arithmetic accessibility theorem.
-/
namespace LogicLineages.OrdinalComparison.TerminationOrdering.Continuation20261117.RawLambdaDynamics.Targets
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedRewriteApplication

/-- A raw finite reduction out of a lambda either ends in same-type bottom,
or retains that lambda and follows exactly a finite reduction of its body. -/
def ActualRawLambdaPathFactorization : Prop :=
  ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
    (Gamma : List Ty) (sigma tau : Ty)
    (body : AuxTerm Symbol arity (sigma :: Gamma) tau)
    (target : AuxTerm Symbol arity Gamma (.arrow sigma tau)),
  RawSteps Symbol arity above Gamma (.arrow sigma tau) (.lam body) target ↔
    target = .bottom (.arrow sigma tau) ∨
      ∃ next : AuxTerm Symbol arity (sigma :: Gamma) tau,
        RawSteps Symbol arity above (sigma :: Gamma) tau body next ∧
        target = .lam next

/-- Literal lambda formation preserves and reflects accessibility for the
original raw numbered reduction, oriented from source to reduct. -/
def ActualRawLambdaAccessibilityEquivalence : Prop :=
  ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
    (Gamma : List Ty) (sigma tau : Ty)
    (body : AuxTerm Symbol arity (sigma :: Gamma) tau),
  Acc (fun successor source =>
    RawStep Symbol arity above Gamma (.arrow sigma tau) source successor)
      (.lam body) ↔
  Acc (fun successor source =>
    RawStep Symbol arity above (sigma :: Gamma) tau source successor) body

end LogicLineages.OrdinalComparison.TerminationOrdering.Continuation20261117.RawLambdaDynamics.Targets
