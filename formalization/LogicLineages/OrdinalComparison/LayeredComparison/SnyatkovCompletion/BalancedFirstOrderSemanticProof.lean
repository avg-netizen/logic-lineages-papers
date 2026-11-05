module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BalancedFirstOrderTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedExactVariablesSemanticProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BaseBooleanSourceSemanticProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BalancedFirstOrderProof
open BalancedFirstOrder

theorem boundEnvironment : BalancedFirstOrderTargets.BoundEnvironment := by
  intro p i ν n hn hp j hj
  by_cases he : j = i
  · subst j
    simpa only [Function.update_self] using hn
  · rw [Function.update_of_ne he]
    apply hp j
    exact List.mem_filter.mpr ⟨hj, by simpa using he⟩

theorem actualSourceTranslation : BalancedFirstOrderTargets.ActualSourceTranslation := by
  intro p
  induction p with
  | compare Γ C E F d =>
    intro hc ν hp
    rw [translate, BaseBooleanSourceProof.exactTranslation]
    exact BalancedExactVariables.Proof.actualSignSemantics Γ C E F d ν hc.1 hc.2.1 hc.2.2 hp
  | negative p ih => intro hc ν hp; exact not_congr (ih hc ν hp)
  | conjunction p q ihp ihq =>
    intro hc ν hp
    have hpl : positive ν p := fun i hi => hp i (List.mem_append_left _ hi)
    have hpr : positive ν q := fun i hi => hp i (List.mem_append_right _ hi)
    exact and_congr (ihp hc.1 ν hpl) (ihq hc.2 ν hpr)
  | existsPositive i p ih =>
    intro hc ν hp
    change (∃ n : Nat, 0 < Function.update ν i n i ∧ (translate p).eval (Function.update ν i n)) ↔ _
    simp only [Function.update_self]
    constructor
    · rintro ⟨n, hn, h⟩
      exact ⟨n, hn, (ih hc _ (boundEnvironment p i ν n hn hp)).mp h⟩
    · rintro ⟨n, hn, h⟩
      exact ⟨n, hn, (ih hc _ (boundEnvironment p i ν n hn hp)).mpr h⟩

theorem exactFreeVariables : BalancedFirstOrderTargets.ExactFreeVariables := by
  intro p
  induction p with
  | compare Γ C E F d =>
    intro i
    rw [translate, (BaseBooleanSourceProof.exactSourceData _).2]
    exact (BalancedExactVariables.Proof.truthAndExactVariables Γ C E F d).2 i
  | negative p ih => exact ih
  | conjunction p q ihp ihq =>
    intro i
    simp only [translate, SourceFormula.variables, Formula.variables, List.mem_append, ihp, ihq]
  | existsPositive i p ih =>
    intro j
    simp only [translate, SourceFormula.variables, CommonLayerSyntax.BaseTerm.variables, Formula.variables,
      List.nil_append, List.mem_filter, List.mem_append, List.mem_singleton, ih,
      bne_iff_ne, ne_eq]
    tauto

theorem exactUniversalDomain : BalancedFirstOrderTargets.ExactUniversalDomain := by
  classical
  intro p hp i ν hν
  have hc : (forallPositive i p).certified := hp
  have hpos : positive ν (forallPositive i p) := hν
  rw [actualSourceTranslation _ hc ν hpos]
  simp only [forallPositive, Formula.eval, not_exists, not_not, not_and] <;> trivial

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BalancedFirstOrderProof
