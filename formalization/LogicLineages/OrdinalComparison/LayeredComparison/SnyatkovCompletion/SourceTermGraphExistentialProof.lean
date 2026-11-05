module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceTermGraphSemanticProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceTermGraphExistentialProof
open CommonLayerSyntax NormalForm SourceTermGraph
open SourceTermGraphSupportProof SourceTermGraphSemanticProof

/-- A finite existential prefix changes precisely its listed names. Repeated
names are allowed: their later assignments shadow their earlier assignments. -/
theorem existsPrefix_iff_frame (ν : Nat → Nat) (xs : List Nat) (p : NormalForm.Formula) :
    existsPrefix ν xs p ↔ ∃ σ : Nat → Nat,
      (∀ i, i ∉ xs → σ i = ν i) ∧ p.eval σ := by
  induction xs generalizing ν with
  | nil =>
      constructor
      · intro hp
        exact ⟨ν, fun _ _ => rfl, hp⟩
      · rintro ⟨σ, hframe, hp⟩
        have he : σ = ν := funext (fun i => hframe i (by simp))
        subst σ
        exact hp
  | cons j xs ih =>
      constructor
      · rintro ⟨n, hn⟩
        obtain ⟨σ, hframe, hp⟩ := (ih (Function.update ν j n)).mp hn
        refine ⟨σ, ?_, hp⟩
        intro i hi
        have hix : i ∉ xs := fun h => hi (List.mem_cons_of_mem j h)
        have hij : i ≠ j := by
          intro he
          apply hi
          simp only [List.mem_cons, he, true_or]
        rw [hframe i hix, Function.update_of_ne hij]
      · rintro ⟨σ, hframe, hp⟩
        refine ⟨σ j, (ih (Function.update ν j (σ j))).mpr ⟨σ, ?_, hp⟩⟩
        intro i hi
        by_cases hij : i = j
        · subst i
          simp only [Function.update_self]
        · rw [Function.update_of_ne hij]
          apply hframe i
          simp only [List.mem_cons, not_or]
          exact ⟨hij, hi⟩

theorem exactExistentialGraph : SourceTermGraphTargets.ExactExistentialGraph := by
  intro start t ν y hf
  rw [existsPrefix_iff_frame]
  constructor
  · intro hvalue
    obtain ⟨σ, hframe, hgraph, hout⟩ := totalGraphRealization start t ν hf
    refine ⟨σ, hframe, ?_⟩
    change (graph start t).eval σ ∧
      (equation (numeralRow (output start t) y)).eval σ
    exact ⟨hgraph, (numeral_equation (output start t) y σ).mpr (hout.trans hvalue)⟩
  · rintro ⟨σ, hframe, hresult⟩
    change (graph start t).eval σ ∧
      (equation (numeralRow (output start t) y)).eval σ at hresult
    have hvalue : t.value σ = t.value ν := source_value_congr t σ ν (by
      intro i hi
      apply hframe i
      intro hnode
      have hlow := hf i hi
      have hrange := (mem_allocated start t i).mp hnode
      omega)
    calc
      t.value ν = t.value σ := hvalue.symm
      _ = σ (output start t) := (graphSoundness start t σ hresult.1).symm
      _ = y := (numeral_equation (output start t) y σ).mp hresult.2

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceTermGraphExistentialProof
