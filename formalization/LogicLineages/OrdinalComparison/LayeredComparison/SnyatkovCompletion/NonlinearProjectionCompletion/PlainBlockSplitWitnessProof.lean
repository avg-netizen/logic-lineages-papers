module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockSplitLinearProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockSplitProof
open BlockRows PlainBlockSplit

theorem extend_frame (bound : List Nat) (i : Nat) (ν τ : Nat → Nat) (n : Nat)
    (hi : i ∈ bound) (hτ : ∀ j, j ∉ bound.erase i → τ j = ν j) :
    ∀ j, j ∉ bound → Function.update τ i n j = ν j := by
  intro j hj
  have hji : j ≠ i := by intro he; subst j; exact hj hi
  rw [Function.update_of_ne hji]
  apply hτ j
  intro he
  exact hj (List.mem_of_mem_erase he)

theorem reset_frame (bound : List Nat) (i : Nat) (ν σ : Nat → Nat)
    (hσ : ∀ j, j ∉ bound → σ j = ν j) :
    ∀ j, j ∉ bound.erase i → Function.update σ i (ν i) j = ν j := by
  intro j hj
  by_cases hji : j = i
  · subst j; simp only [Function.update_self]
  · rw [Function.update_of_ne hji]
    apply hσ j
    intro he
    exact hj ((List.mem_erase_of_ne hji).mpr he)

theorem restore_update (σ : Nat → Nat) (i n : Nat) :
    Function.update (Function.update σ i n) i (σ i) = σ := by
  funext j
  by_cases hji : j = i
  · subst j; simp only [Function.update_self]
  · simp only [Function.update_of_ne hji]

theorem substitution_sound (bound : List Nat) (p : Formula) (i : Nat) (t : Term)
    (ν : Nat → Nat) (hi : i ∈ bound)
    (h : existsPrefix ν (bound.erase i) (p.substitute i t)) : existsPrefix ν bound p := by
  obtain ⟨τ, hτ, hp⟩ := (existsPrefix_iff_frame ν (bound.erase i) _).mp h
  apply (existsPrefix_iff_frame ν bound p).mpr
  exact ⟨Function.update τ i (t.value τ), extend_frame bound i ν τ (t.value τ) hi hτ,
    (BlockRowsProof.formula_substitution p i t τ).mp hp⟩

theorem substitution_complete (bound : List Nat) (p : Formula) (i : Nat) (t : Term)
    (ν σ : Nat → Nat) (hσ : ∀ j, j ∉ bound → σ j = ν j) (hp : p.eval σ)
    (ht : i ∉ t.variables) (hvalue : t.value σ = σ i) :
    existsPrefix ν (bound.erase i) (p.substitute i t) := by
  let τ := Function.update σ i (ν i)
  have htau : t.value τ = t.value σ := WindowProof.term_update t i (ν i) σ ht
  have hrestore : Function.update τ i (t.value τ) = σ := by
    rw [htau, hvalue]
    exact restore_update σ i (ν i)
  apply (existsPrefix_iff_frame ν (bound.erase i) _).mpr
  refine ⟨τ, reset_frame bound i ν σ hσ, ?_⟩
  apply (BlockRowsProof.formula_substitution p i t τ).mpr
  rw [hrestore]
  exact hp

theorem tie_sound (bound : List Nat) (p : Formula) (i j : Nat) (ν : Nat → Nat)
    (hi : i ∈ bound) (hparams : i ∉ p.parameters)
    (h : existsPrefix ν (bound.erase i) (rename i j p)) : existsPrefix ν bound p := by
  obtain ⟨τ, hτ, hp⟩ := (existsPrefix_iff_frame ν (bound.erase i) _).mp h
  apply (existsPrefix_iff_frame ν bound p).mpr
  exact ⟨Function.update τ i (τ j), extend_frame bound i ν τ (τ j) hi hτ,
    (literalTieSemantics p i j hparams τ).mp hp⟩

theorem tie_complete (bound : List Nat) (p : Formula) (i j : Nat) (ν σ : Nat → Nat)
    (hσ : ∀ k, k ∉ bound → σ k = ν k) (hp : p.eval σ)
    (hparams : i ∉ p.parameters) (hji : j ≠ i) (heq : σ j = σ i) :
    existsPrefix ν (bound.erase i) (rename i j p) := by
  let τ := Function.update σ i (ν i)
  have htau : τ j = σ j := Function.update_of_ne hji (ν i) σ
  have hrestore : Function.update τ i (τ j) = σ := by
    rw [htau, heq]
    exact restore_update σ i (ν i)
  apply (existsPrefix_iff_frame ν (bound.erase i) _).mpr
  refine ⟨τ, reset_frame bound i ν σ hσ, ?_⟩
  apply (literalTieSemantics p i j hparams τ).mpr
  rw [hrestore]
  exact hp

private theorem calibrated_prefix_sound (bound : List Nat) (p q f o : Formula) (i : Nat)
    (ν : Nat → Nat) (hi : i ∈ bound)
    (hcal : ∀ τ : Nat → Nat, q.eval τ ↔ ∃ n : Nat,
      f.eval (Function.update τ i n) ∧ o.eval (Function.update τ i n) ∧
        p.eval (Function.update τ i n))
    (h : existsPrefix ν (bound.erase i) q) : existsPrefix ν bound p := by
  obtain ⟨τ, hτ, hp⟩ := (existsPrefix_iff_frame ν (bound.erase i) _).mp h
  obtain ⟨n, _, _, hbody⟩ := (hcal τ).mp hp
  apply (existsPrefix_iff_frame ν bound p).mpr
  exact ⟨Function.update τ i n, extend_frame bound i ν τ n hi hτ, hbody⟩

private theorem calibrated_prefix_complete (bound : List Nat) (p q f o : Formula) (i : Nat)
    (ν σ : Nat → Nat)
    (hcal : ∀ τ : Nat → Nat, q.eval τ ↔ ∃ n : Nat,
      f.eval (Function.update τ i n) ∧ o.eval (Function.update τ i n) ∧
        p.eval (Function.update τ i n))
    (hσ : ∀ j, j ∉ bound → σ j = ν j) (hp : p.eval σ)
    (hf : f.eval σ) (ho : o.eval σ) : existsPrefix ν (bound.erase i) q := by
  let τ := Function.update σ i (ν i)
  apply (existsPrefix_iff_frame ν (bound.erase i) _).mpr
  refine ⟨τ, reset_frame bound i ν σ hσ, ?_⟩
  apply (hcal τ).mpr
  refine ⟨σ i, ?_⟩
  have he : Function.update τ i (σ i) = σ := restore_update σ i (ν i)
  rw [he]
  exact ⟨hf, ho, hp⟩

/-- Apply the already proved ACTUAL outside projection at an opaque logical
boundary, so prefix transport does not normalize its Cooper implementation. -/
theorem far_sound (bound : List Nat) (p : Formula) (i : Nat) (ν : Nat → Nat)
    (hi : i ∈ bound) (hallowed : TiedLinear.allowed bound p = true)
    (hparams : ParametersIndependent bound p)
    (h : existsPrefix ν (bound.erase i)
      (TiedLinear.eliminate i
        (.conjunction (frame bound i p) (.conjunction (outside i p) (linearize i p))))) :
    existsPrefix ν bound p :=
  calibrated_prefix_sound bound p _ (frame bound i p) (outside i p) i ν hi
    (far_branch_meaning bound p i hi hallowed hparams) h

theorem far_complete (bound : List Nat) (p : Formula) (i : Nat) (ν σ : Nat → Nat)
    (hi : i ∈ bound) (hallowed : TiedLinear.allowed bound p = true)
    (hparams : ParametersIndependent bound p)
    (hσ : ∀ j, j ∉ bound → σ j = ν j) (hp : p.eval σ)
    (hframe : (frame bound i p).eval σ) (hout : (outside i p).eval σ) :
    existsPrefix ν (bound.erase i)
      (TiedLinear.eliminate i
        (.conjunction (frame bound i p) (.conjunction (outside i p) (linearize i p)))) :=
  calibrated_prefix_complete bound p _ (frame bound i p) (outside i p) i ν σ
    (far_branch_meaning bound p i hi hallowed hparams) hσ hp hframe hout

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockSplitProof
