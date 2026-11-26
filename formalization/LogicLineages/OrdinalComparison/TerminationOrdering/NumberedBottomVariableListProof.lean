module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomVariableProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomVariableListProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedPrimarySubstitution

/-- Lift a permutation of a mapped list by rearranging original occurrences.
No injectivity of f is needed or used. -/
theorem mapPermutationInverse {alpha beta : Type} (f : alpha → beta)
    (source : List alpha) (target : List beta) (h : (source.map f).Perm target) :
    ∃ lifted : List alpha, source.Perm lifted ∧ lifted.map f = target := by
  have hc : Relation.Comp (fun a b => a = List.map f b) List.Perm target source := by
    rw [List.eq_map_comp_perm]
    exact h.symm
  obtain ⟨lifted,he,hp⟩ := hc
  exact ⟨lifted,hp.symm,he.symm⟩

theorem mapAppendSplit {alpha beta : Type} (f : alpha → beta)
    (source : List alpha) (left right : List beta) (h : source.map f = left ++ right) :
    ∃ left' right' : List alpha,
      source = left' ++ right' ∧ left'.map f = left ∧ right'.map f = right := by
  induction left generalizing source with
  | nil => exact ⟨[],source,rfl,rfl,h⟩
  | cons x left ih =>
    cases source with
    | nil => cases h
    | cons y source =>
      change f y :: source.map f = x :: (left ++ right) at h
      obtain ⟨hy,hs⟩ := List.cons.inj h
      obtain ⟨left',right',he,hl,hr⟩ := ih source hs
      exact ⟨y :: left',right',by simp only [he,List.cons_append],
        by simp only [List.map_cons,hy,hl],hr⟩

/-- A preimage list of the actual packed argument list retains every type and
therefore reconstructs an actual typed tuple in the original context. -/
theorem argumentListInverse {Symbol : Type} {arity : Symbol → Nat} {Gamma Delta : List Ty}
    (theta : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta)
    (types : List Ty) (target : AuxArguments Symbol arity Delta types)
    (values : List (Packed Symbol arity Gamma))
    (h : values.map (substitutePacked theta) = argumentList target) :
    ∃ source : AuxArguments Symbol arity Gamma types,
      argumentList source = values ∧ substituteArguments source theta = target := by
  induction types generalizing values with
  | nil =>
    cases target
    have he : values = [] := List.map_eq_nil_iff.mp h
    subst values
    exact ⟨.nil,rfl,rfl⟩
  | cons sigma types ih =>
    cases target with
    | cons q rest =>
      cases values with
      | nil => cases h
      | cons p values =>
        rcases p with ⟨tau,p⟩
        change substitutePacked theta ⟨tau,p⟩ :: values.map (substitutePacked theta) =
          ⟨sigma,q⟩ :: argumentList rest at h
        obtain ⟨hp,hr⟩ := List.cons.inj h
        have htype : tau = sigma := congrArg Sigma.fst hp
        cases htype
        have hterm : substitute p theta = q := by injection hp
        obtain ⟨source,hs,he⟩ := ih rest values hr
        refine ⟨.cons p source,?_,?_⟩
        · exact congrArg (List.cons (⟨sigma,p⟩ : Packed Symbol arity Gamma)) hs
        · simp only [substituteArguments,hterm,he]

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomVariableListProof
