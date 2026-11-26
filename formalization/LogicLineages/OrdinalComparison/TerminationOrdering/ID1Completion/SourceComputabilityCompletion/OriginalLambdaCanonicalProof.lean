module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaCanonicalSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaCanonicalProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse
open NumberedAuxiliaryCoding NumberedLeastCodeRepresentative OriginalLambdaCanonical
open OriginalLambdaCanonicalTargets OriginalLambdaCanonicalSupportProof

theorem actualOriginalLambdaRepresentativeFactorization :
    ActualOriginalLambdaRepresentativeFactorization := by
  intro n arity symbols S hc Gamma sigma tau body hlambda
  obtain ⟨body',_,_,he,_,hl⟩ :=
    typedLambdaRepresentative n arity symbols S hc Gamma sigma tau body hlambda
  rw [hl,he]
  simp only [lambdaPacked,packedNumber,termCode,codeNumber,Nat.unpair_pair]

theorem actualOriginalLambdaCanonicalBodyIff : ActualOriginalLambdaCanonicalBodyIff := by
  intro n arity symbols S hc Gamma sigma tau body hlambda
  obtain ⟨body',_,_,he,_,hl⟩ :=
    typedLambdaRepresentative n arity symbols S hc Gamma sigma tau body hlambda
  rw [hl,he]
  constructor
  · intro h
    change Nat.pair (typeNumber (.arrow sigma tau))
        (Nat.pair 1 (Nat.pair (typeNumber sigma) (codeNumber (termCode body')))) =
      Nat.pair (typeNumber (.arrow sigma tau))
        (Nat.pair 1 (Nat.pair (typeNumber sigma) (codeNumber (termCode body)))) at h
    have hp := (Nat.pair_eq_pair.mp (Nat.pair_eq_pair.mp (Nat.pair_eq_pair.mp h).2).2).2
    exact congrArg (Nat.pair (typeNumber tau)) hp
  · intro h
    change Nat.pair (typeNumber tau) (codeNumber (termCode body')) =
      Nat.pair (typeNumber tau) (codeNumber (termCode body)) at h
    exact congrArg (fun k => Nat.pair (typeNumber (.arrow sigma tau))
      (Nat.pair 1 (Nat.pair (typeNumber sigma) k))) (Nat.pair_eq_pair.mp h).2

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaCanonicalProof
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaCanonicalProof
