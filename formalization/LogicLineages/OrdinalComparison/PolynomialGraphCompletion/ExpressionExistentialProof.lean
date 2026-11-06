module
public import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.Targets
public import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.ExpressionTargets
import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.ExpressionSupportProof
import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.ExpressionNodeProof
import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.ExpressionRealizationProof

public section
namespace LogicLineages.OrdinalComparison.PolynomialGraphCompletion.ExpressionExistentialProof
open ExpressionSupportProof ExpressionNodeProof ExpressionRealizationProof

/-- The finite natural existential prefix changes exactly its allocated
names. This characterization does not add any free input or witness oracle. -/
theorem existsNodes_iff_frame (ν : Nat → Nat) (xs : List Nat) (rs : List Row) :
    existsNodes ν xs rs ↔ ∃ σ : Nat → Nat,
      (∀ i, i ∉ xs → σ i = ν i) ∧ RowsHold rs σ := by
  induction xs generalizing ν with
  | nil =>
      constructor
      · intro h
        exact ⟨ν,fun _ _ => rfl,h⟩
      · rintro ⟨σ,hframe,h⟩
        have he : σ = ν := funext (fun i => hframe i (by simp))
        subst σ
        exact h
  | cons j xs ih =>
      constructor
      · rintro ⟨n,hn⟩
        obtain ⟨σ,hframe,h⟩ := (ih (Function.update ν j n)).mp hn
        refine ⟨σ,?_,h⟩
        intro i hi
        have hix : i ∉ xs := fun hm => hi (List.mem_cons_of_mem j hm)
        have hij : i ≠ j := by
          intro he
          apply hi
          simp only [List.mem_cons,he,true_or]
        rw [hframe i hix,Function.update_of_ne hij]
      · rintro ⟨σ,hframe,h⟩
        refine ⟨σ j,(ih (Function.update ν j (σ j))).mpr ⟨σ,?_,h⟩⟩
        intro i hi
        by_cases hij : i = j
        · subst i
          simp only [Function.update_self]
        · rw [Function.update_of_ne hij]
          apply hframe i
          simp only [List.mem_cons,not_or]
          exact ⟨hij,hi⟩

theorem correlatedExistentialGraph (hHead : Targets.HeadEquationExact) :
    ExpressionTargets.CorrelatedExistentialGraph := by
  intro t ht resultName ν
  let start := freshStart t resultName
  have hf : Fresh start t := (freshSymbolicOutput t resultName).1
  have hresult : resultName ∉ allocated start t := (freshSymbolicOutput t resultName).2.2
  change existsNodes ν (allocated start t) (graphRows t resultName) ↔
    ν resultName = t.value ν
  rw [existsNodes_iff_frame]
  constructor
  · rintro ⟨σ,hframe,hrows⟩
    obtain ⟨hgraph,hlink⟩ :=
      (rows_hold_append (rows start t) [variableRow resultName (output start t)] σ).mp hrows
    have hlinkValue := (rows_hold_singleton (variableRow resultName (output start t)) σ).mp hlink
    have heq := (variable_equation resultName (output start t) σ).mp hlinkValue.2
    calc
      ν resultName = σ resultName := (hframe resultName hresult).symm
      _ = σ (output start t) := heq
      _ = t.value σ := graphSoundness hHead start t ht σ hgraph
      _ = t.value ν := source_frame t t start ν σ hf hframe
  · intro hvalue
    obtain ⟨σ,hframe,hgraph,hout⟩ := totalGraphRealization hHead start t ht ν hf
    refine ⟨σ,hframe,?_⟩
    apply (rows_hold_append (rows start t) [variableRow resultName (output start t)] σ).mpr
    refine ⟨hgraph,(rows_hold_singleton (variableRow resultName (output start t)) σ).mpr ?_⟩
    refine ⟨variable_domain resultName (output start t) σ,?_⟩
    apply (variable_equation resultName (output start t) σ).mpr
    calc
      σ resultName = ν resultName := hframe resultName hresult
      _ = t.value ν := hvalue
      _ = σ (output start t) := hout.symm

theorem totalFunctionalGraph (hHead : Targets.HeadEquationExact) :
    ExpressionTargets.TotalFunctionalGraph := by
  intro t ht resultName hresult ν
  have hvalue (y : Nat) :
      t.value (Function.update ν resultName y) = t.value ν := by
    apply source_value_congr
    intro i hi
    have hne : i ≠ resultName := by
      intro he
      exact hresult (he ▸ hi)
    exact Function.update_of_ne hne _ _
  have hmeaning (y : Nat) :
      expressionGraph t resultName (Function.update ν resultName y) ↔ y = t.value ν := by
    rw [correlatedExistentialGraph hHead t ht resultName _,Function.update_self,hvalue y]
  exact ⟨t.value ν,(hmeaning _).mpr rfl,fun y hy => (hmeaning y).mp hy⟩

end LogicLineages.OrdinalComparison.PolynomialGraphCompletion.ExpressionExistentialProof
