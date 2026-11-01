module
public import LogicLineages.OrdinalComparison.SuccessorNormalizationInvariantDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-- Every iterate of the ACTUAL numeric normalization trace is a faithful
source state with exact counts/domains and a proved progress-or-stop budget. -/
def ActualSuccessorNormalizationTraceInvariant : Prop :=
  ∀ (w : List (NONote × Nat)) (E : FixedLimitPositiveExpr) (eta lower : NONote) (c : Nat),
    oneVariableComparisonValid (.range (w++[(eta,c)]) E) →
    0<lower.1.repr → lower.1.repr<eta.1.repr → ∀ k : Nat,
    SuccessorNormalizationSourceInvariant w E eta lower c k
      (encodedSuccessorNormalizationTrace (oneVariableComparisonEncode (.range w E))
        (rawNoteEncode eta.1) (rawNoteEncode lower.1) c k)

end LogicLineages.OrdinalComparison.Targets
