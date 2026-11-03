module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedSubstitutionDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedSubstitutionTargets
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding RecursiveComparison SourceExtendedSubstitution

/-- Actual auxiliary reflexivity includes arbitrary marked intermediates. -/
def ActualReflexivity : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (above : Symbol → Symbol → Prop) (Gamma : List Ty) (tau : Ty) (q : MarkedTerm Symbol arity Gamma tau),
  SourceExtendedComparison.Weak Symbol arity above Gamma ⟨tau,q⟩ ⟨tau,q⟩

/-- Genuine five-way auxiliary covariance under ANY marked typed substitution.
Every finite macro, actual successful full-tuple Select and binder opening must
be paid by the actual derivation induction; no supplied transport callback. -/
def ActualJointCovariance : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop),
  (∀ Gamma (s t : Packed Symbol arity Gamma),SourceExtendedComparison.Weak Symbol arity above Gamma s t →
    ∀ Delta (theta : MarkedSubstitution Symbol arity Gamma Delta),SourceExtendedComparison.Weak Symbol arity above Delta
      (substitutePacked theta s) (substitutePacked theta t)) ∧
  (∀ Gamma (s t : Packed Symbol arity Gamma),SourceExtendedComparison.Strict Symbol arity above Gamma s t →
    ∀ Delta (theta : MarkedSubstitution Symbol arity Gamma Delta),SourceExtendedComparison.Strict Symbol arity above Delta
      (substitutePacked theta s) (substitutePacked theta t)) ∧
  (∀ Gamma (ss ts : List (Packed Symbol arity Gamma)),SourceExtendedComparison.WeakMatch Symbol arity above Gamma ss ts →
    ∀ Delta (theta : MarkedSubstitution Symbol arity Gamma Delta),SourceExtendedComparison.WeakMatch Symbol arity above Delta
      (ss.map (substitutePacked theta)) (ts.map (substitutePacked theta))) ∧
  (∀ Gamma (ss ts : List (Packed Symbol arity Gamma)),SourceExtendedComparison.StrictMultiset Symbol arity above Gamma ss ts →
    ∀ Delta (theta : MarkedSubstitution Symbol arity Gamma Delta),SourceExtendedComparison.StrictMultiset Symbol arity above Delta
      (ss.map (substitutePacked theta)) (ts.map (substitutePacked theta))) ∧
  (∀ Gamma (ss ts : List (Packed Symbol arity Gamma)),SourceExtendedComparison.ReplacementMatch Symbol arity above Gamma ss ts →
    ∀ Delta (theta : MarkedSubstitution Symbol arity Gamma Delta),SourceExtendedComparison.ReplacementMatch Symbol arity above Delta
      (ss.map (substitutePacked theta)) (ts.map (substitutePacked theta)))

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedSubstitutionTargets
