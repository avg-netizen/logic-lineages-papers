module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomVariableLiftingTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomVariableListProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimarySubstitutionProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomVariableExchangeSupportProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedPrimarySubstitution
open NumberedBottomVariableListProof NumberedPrimarySubstitutionProof

theorem typedWitness {Symbol : Type} {arity : Symbol → Nat} {Gamma Delta : List Ty}
    (theta : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta)
    (R : Packed Symbol arity Gamma → Prop) (tau : Ty) (r : AuxTerm Symbol arity Delta tau)
    (h : ∃ p : Packed Symbol arity Gamma, R p ∧ substitutePacked theta p = ⟨tau,r⟩) :
    ∃ q : AuxTerm Symbol arity Gamma tau, R ⟨tau,q⟩ ∧ substitute q theta = r := by
  obtain ⟨⟨rho,q⟩,hq,he⟩ := h
  have ht : rho = tau := congrArg Sigma.fst he
  cases ht
  exact ⟨q,hq,by injection he⟩

theorem argumentPermutationInverse {Symbol : Type} {arity : Symbol → Nat} {Gamma Delta : List Ty}
    (theta : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta)
    {sourceTypes targetTypes : List Ty} (base : AuxArguments Symbol arity Gamma sourceTypes)
    (target : AuxArguments Symbol arity Delta targetTypes)
    (h : (argumentList (substituteArguments base theta)).Perm (argumentList target)) :
    ∃ source : AuxArguments Symbol arity Gamma targetTypes,
      (argumentList base).Perm (argumentList source) ∧ substituteArguments source theta = target := by
  rw [argumentListSubstitute] at h
  obtain ⟨values,hperm,hmap⟩ := mapPermutationInverse (substitutePacked theta) (argumentList base) (argumentList target) h
  obtain ⟨source,hlist,he⟩ := argumentListInverse theta _ target values hmap
  exact ⟨source,hlist.symm ▸ hperm,he⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomVariableExchangeSupportProof
