module
public import LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.SemanticProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.Proof
open PolynomialGraphCompletion LayeredComparison.SnyatkovCompletion

theorem lift_variables (x : Nat) (p : Formula) :
    (liftFormula x p).variables = p.tokens.map (tokenName x) := by
  induction p with
  | bot => rfl
  | top => rfl
  | atom a =>
      cases a <;>
        simp [liftFormula, liftAtom, liftRow, NormalForm.Formula.variables,
          NormalForm.Atom.row, NormalForm.rowVariables, NormalForm.Summand.name, Formula.tokens,
          LogicLineages.ModelsAlgebra.Forests.CotreePresburgerUnit.Boolean.atoms,
          Atom.row, List.map_map, Function.comp_def]
  | neg p ih => exact ih
  | conj p q ihp ihq =>
      simp only [liftFormula, NormalForm.Formula.variables, ihp, ihq,
        Formula.tokens, LogicLineages.ModelsAlgebra.Forests.CotreePresburgerUnit.Boolean.atoms,
        List.flatMap_append, List.map_append]
  | disj p q ihp ihq =>
      simp only [liftFormula, NormalForm.Formula.variables, ihp, ihq,
        Formula.tokens, LogicLineages.ModelsAlgebra.Forests.CotreePresburgerUnit.Boolean.atoms,
        List.flatMap_append, List.map_append]

theorem lower_row_tokens (x : Nat) (r : NormalForm.Row) (hr : PureRow r) :
    (lowerRow x r).2.map Prod.snd = (NormalForm.rowVariables r).map (tokenOfName x) := by
  simp only [lowerRow, NormalForm.rowVariables, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro a ha
  obtain ⟨j, hj⟩ := hr a ha
  simp only [hj, lowerSummand, NormalForm.Summand.name]

theorem lower_tokens (x : Nat) (p : NormalForm.Formula) (hp : PureFormula p) :
    (lowerFormula x p).tokens = p.variables.map (tokenOfName x) := by
  induction p with
  | truth => rfl
  | falsity => rfl
  | atom a =>
      cases a with
      | nonnegative r =>
          change PureRow r at hp
          simpa only [lowerFormula, lowerAtom, Formula.tokens,
            LogicLineages.ModelsAlgebra.Forests.CotreePresburgerUnit.Boolean.atoms,
            List.flatMap_cons, List.flatMap_nil, List.append_nil, Atom.row,
            NormalForm.Formula.variables, NormalForm.Atom.row] using lower_row_tokens x r hp
      | divisible m r =>
          change PureRow r at hp
          simpa only [lowerFormula, lowerAtom, Formula.tokens,
            LogicLineages.ModelsAlgebra.Forests.CotreePresburgerUnit.Boolean.atoms,
            List.flatMap_cons, List.flatMap_nil, List.append_nil, Atom.row,
            NormalForm.Formula.variables, NormalForm.Atom.row] using lower_row_tokens x r hp
  | negative p ih => exact ih hp
  | conjunction p q ihp ihq =>
      simp only [lowerFormula, Formula.tokens,
        LogicLineages.ModelsAlgebra.Forests.CotreePresburgerUnit.Boolean.atoms,
        List.flatMap_append, NormalForm.Formula.variables, List.map_append]
      exact congrArg₂ List.append (ihp hp.1) (ihq hp.2)
  | disjunction p q ihp ihq =>
      simp only [lowerFormula, Formula.tokens,
        LogicLineages.ModelsAlgebra.Forests.CotreePresburgerUnit.Boolean.atoms,
        List.flatMap_append, NormalForm.Formula.variables, List.map_append]
      exact congrArg₂ List.append (ihp hp.1) (ihq hp.2)

theorem exactOutputTokens : Targets.ExactOutputTokens := by
  intro x p hp t
  change t ∈ (lowerFormula x (LinearRows.eliminate 0 (liftFormula x p))).tokens ↔ _
  rw [lower_tokens x _ (pure_word_eliminator x p)]
  constructor
  · intro ht
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ht
    obtain ⟨hj0, hj⟩ := (LinearRowsSupportProof.exactOutputSupport 0 (liftFormula x p) j).mp hj
    rw [lift_variables] at hj
    obtain ⟨u, hu, hname⟩ := List.mem_map.mp hj
    subst j
    rw [token_roundtrip]
    refine ⟨?_, hu⟩
    intro hux
    have hw := linear_token x p hp u hu hux
    have heq : u = (x, []) := Prod.ext hux hw
    exact hj0 ((token_name_zero x u).mpr heq)
  · rintro ⟨htx, ht⟩
    refine List.mem_map.mpr ⟨tokenName x t, ?_, token_roundtrip x t⟩
    apply (LinearRowsSupportProof.exactOutputSupport 0 (liftFormula x p) (tokenName x t)).mpr
    refine ⟨?_, ?_⟩
    · intro hz
      exact htx (congrArg Prod.fst ((token_name_zero x t).mp hz))
    · rw [lift_variables]
      exact List.mem_map.mpr ⟨t, ht, rfl⟩

theorem exactOutputVariables : Targets.ExactOutputVariables := by
  intro x p hp i
  simp only [Formula.variables, List.mem_map]
  constructor
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨htx, ht⟩ := (exactOutputTokens x p hp t).mp ht
    exact ⟨htx, t, ht, rfl⟩
  · rintro ⟨hix, t, ht, hti⟩
    refine ⟨t, (exactOutputTokens x p hp t).mpr ⟨?_, ht⟩, hti⟩
    simpa only [hti] using hix

theorem domain_update (x : Nat) (p : Formula) (hp : linear x p = true)
    (ν : Nat → Nat) (n : Nat) :
    p.meaningful (Function.update ν x n) ↔ p.meaningful ν := by
  apply forall_congr'
  intro t
  apply forall_congr'
  intro ht
  by_cases hx : t.1 = x
  · have hw := linear_token x p hp t ht hx
    simp only [hw, WordDomain]
  · rw [Function.update_of_ne hx]

theorem exactOriginalDomains : Targets.ExactOriginalDomains := by
  intro x p hp ν
  constructor
  · intro h t ht
    by_cases hx : t.1 = x
    · have hw := linear_token x p hp t ht hx
      simp only [hw, WordDomain]
    · exact h t ((exactOutputTokens x p hp t).mpr ⟨hx, ht⟩)
  · intro h t ht
    exact h t ((exactOutputTokens x p hp t).mp ht).2

theorem exactDegreePreservation : Targets.ExactDegreePreservation := by
  intro D x p hp h t ht
  exact h t ((exactOutputTokens x p hp t).mp ht).2

theorem domainAwareElimination : Targets.DomainAwareElimination := by
  intro x p hp ν
  rw [exactOriginalDomains x p hp ν, actualWordLinearElimination x p hp ν]
  constructor
  · rintro ⟨hd, n, hn⟩
    exact ⟨n, (domain_update x p hp ν n).mpr hd, hn⟩
  · rintro ⟨n, hd, hn⟩
    exact ⟨(domain_update x p hp ν n).mp hd, n, hn⟩

end LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.Proof
