module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedRelatedSubstitutionDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedRelatedSubstitutionTargets
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding RecursiveComparison SourceExtendedSubstitution SourceExtendedRelatedSubstitution

/-- Full real two-environment version of the source related-substitution
lemma, for all five relations and actual arbitrary typed marked images.
No transitivity, unary currying or generic application callback is assumed. -/
def ActualJointRelatedCovariance : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop),
  (∀ Gamma (s t : Packed Symbol arity Gamma),SourceExtendedComparison.Weak Symbol arity above Gamma s t →
    ∀ Delta (theta eta : MarkedSubstitution Symbol arity Gamma Delta),EnvironmentsRelated above theta eta →
      SourceExtendedComparison.Weak Symbol arity above Delta (substitutePacked theta s) (substitutePacked eta t)) ∧
  (∀ Gamma (s t : Packed Symbol arity Gamma),SourceExtendedComparison.Strict Symbol arity above Gamma s t →
    ∀ Delta (theta eta : MarkedSubstitution Symbol arity Gamma Delta),EnvironmentsRelated above theta eta →
      SourceExtendedComparison.Strict Symbol arity above Delta (substitutePacked theta s) (substitutePacked eta t)) ∧
  (∀ Gamma (ss ts : List (Packed Symbol arity Gamma)),SourceExtendedComparison.WeakMatch Symbol arity above Gamma ss ts →
    ∀ Delta (theta eta : MarkedSubstitution Symbol arity Gamma Delta),EnvironmentsRelated above theta eta →
      SourceExtendedComparison.WeakMatch Symbol arity above Delta (ss.map (substitutePacked theta)) (ts.map (substitutePacked eta))) ∧
  (∀ Gamma (ss ts : List (Packed Symbol arity Gamma)),SourceExtendedComparison.StrictMultiset Symbol arity above Gamma ss ts →
    ∀ Delta (theta eta : MarkedSubstitution Symbol arity Gamma Delta),EnvironmentsRelated above theta eta →
      SourceExtendedComparison.StrictMultiset Symbol arity above Delta (ss.map (substitutePacked theta)) (ts.map (substitutePacked eta))) ∧
  (∀ Gamma (ss ts : List (Packed Symbol arity Gamma)),SourceExtendedComparison.ReplacementMatch Symbol arity above Gamma ss ts →
    ∀ Delta (theta eta : MarkedSubstitution Symbol arity Gamma Delta),EnvironmentsRelated above theta eta →
      SourceExtendedComparison.ReplacementMatch Symbol arity above Delta (ss.map (substitutePacked theta)) (ts.map (substitutePacked eta)))

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedRelatedSubstitutionTargets
