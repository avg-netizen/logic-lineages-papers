module

public import LogicLineages.ComputabilityKnowledge.Comparators.CircuitComparison
public import LogicLineages.ComputabilityKnowledge.CircuitReductionProof
public import LogicLineages.ComputabilityKnowledge.ExponentialGapProof
public import LogicLineages.ComputabilityKnowledge.PositiveExpressionProperties

@[expose] public section

/-! External Codex continuation proof of the frozen finite-variable comparison
component. Effectivity, polynomial translation and MRDP have separate targets. -/
namespace LogicLineages.ComputabilityKnowledge.CircuitComparisonProof

open PositiveExpression CircuitReduction CircuitComparison
open Comparators.ExponentialGap

private theorem finiteVal_at {d : Nat} (ρ : Fin d → PosNat) (i : Fin d) :
    finiteVal ρ i.val = ρ i := by simp [finiteVal, i.isLt]

private theorem eval_bounded (e : Expr Nat) (d : Nat) (ρ τ : Nat → PosNat)
    (he : Bounded d e) (h : ∀ j, j < d → ρ j = τ j) : e.eval ρ = e.eval τ := by
  induction e with
  | one => rfl
  | var j => exact congrArg Subtype.val (h j he)
  | add a b ha hb =>
    change a.eval ρ + b.eval ρ = a.eval τ + b.eval τ
    rw [ha he.1, hb he.2]
  | emul a b ha hb =>
    change 2 ^ a.eval ρ * b.eval ρ = 2 ^ a.eval τ * b.eval τ
    rw [ha he.1, hb he.2]

theorem fixedInputs : Comparators.CircuitComparison.FixedInputs := by
  intro c hc ρ
  constructor
  · intro h
    obtain ⟨ν, hν, hs⟩ := (CircuitReductionProof.correctness c hc (finiteVal ρ)).mp h
    let τ : Fin (variableBound c) → PosNat := fun j => ν j.val
    have hext : ∀ j, j < variableBound c → finiteVal τ j = ν j := by
      intro j hj
      exact finiteVal_at τ ⟨j,hj⟩
    refine ⟨τ, ?_, ?_⟩
    · intro j
      rw [hext j.val (by have := j.isLt; simp only [variableBound]; omega), hν j.val j.isLt]
      exact finiteVal_at ρ j
    · apply (ExponentialGapProof.systemCollision (finiteVal τ) (compile c)).2.mpr
      intro p hp
      obtain ⟨hl,hr⟩ := CircuitReductionProof.variablesBounded c hc p hp
      rw [eval_bounded p.1 _ (finiteVal τ) ν hl hext,
        eval_bounded p.2 _ (finiteVal τ) ν hr hext]
      exact hs p hp
  · rintro ⟨τ, ha, he⟩
    apply (CircuitReductionProof.correctness c hc (finiteVal ρ)).mpr
    refine ⟨finiteVal τ, ?_, ?_⟩
    · intro j hj
      rw [ha ⟨j,hj⟩, finiteVal_at ρ ⟨j,hj⟩]
    · exact (ExponentialGapProof.systemCollision (finiteVal τ) (compile c)).2.mp he

theorem equalityWitness : Comparators.CircuitComparison.EqualityWitness := by
  intro c hc
  constructor
  · rintro ⟨ρ,hρ⟩
    obtain ⟨τ, _, he⟩ := (fixedInputs c hc ρ).mp hρ
    exact ⟨τ, he⟩
  · rintro ⟨τ,he⟩
    let ρ : Fin c.inputCount → PosNat := fun j => finiteVal τ j.val
    exact ⟨ρ, (fixedInputs c hc ρ).mpr ⟨τ, fun _ => rfl, he⟩⟩

theorem alwaysOrdered : Comparators.CircuitComparison.AlwaysOrdered := by
  intro c _ τ
  exact (ExponentialGapProof.systemCollision (finiteVal τ) (compile c)).1

theorem strictReduction : Comparators.CircuitComparison.StrictReduction := by
  intro c hc
  constructor
  · intro h τ
    have hne : (upper c).eval (finiteVal τ) ≠ (lower c).eval (finiteVal τ) := by
      intro he
      exact h ((equalityWitness c hc).mpr ⟨τ, he⟩)
    have hle := alwaysOrdered c hc τ
    omega
  · intro h hs
    obtain ⟨τ,he⟩ := (equalityWitness c hc).mp hs
    have hlt := h τ
    omega

theorem weakReduction : Comparators.CircuitComparison.WeakReduction := by
  intro c hc
  rw [strictReduction c hc]
  constructor
  · intro h τ
    change (lower c).eval (finiteVal τ) + 1 ≤ (upper c).eval (finiteVal τ)
    exact h τ
  · intro h τ
    exact h τ

theorem depthBound : Comparators.CircuitComparison.DepthBound := by
  intro c hc
  have h := PositiveExpressionProperties.system_depth (compile c)
    (CircuitReductionProof.depthBound c hc)
  refine ⟨h.1,h.2,?_⟩
  change max (lower c).depth 0 ≤ 2
  change (upper c).depth ≤ 2 ∧ (lower c).depth ≤ 2 at h
  omega

private theorem system_bounded (s : System) (d : Nat)
    (h : ∀ p ∈ s, Bounded d p.1 ∧ Bounded d p.2) :
    Bounded d (systemLeft s) ∧ Bounded d (systemRight s) := by
  induction s with
  | nil => exact ⟨trivial,trivial⟩
  | cons p ps ih =>
    have hp := h p (by simp)
    have hps := ih (fun p hp => h p (List.mem_cons_of_mem _ hp))
    rcases p with ⟨a,b⟩
    simp only [systemLeft,systemRight,leftPair,rightPair,Bounded]
    refine ⟨⟨?_,hps.1⟩,⟨?_,hps.2⟩⟩
    · exact ⟨⟨⟨hp.1,hp.1⟩,trivial⟩,⟨⟨hp.2,hp.2⟩,trivial⟩⟩
    · exact ⟨⟨⟨hp.1,hp.2⟩,trivial⟩,trivial⟩

theorem variablesBounded : Comparators.CircuitComparison.VariablesBounded := by
  intro c hc
  have h := system_bounded (compile c) (variableBound c)
    (CircuitReductionProof.variablesBounded c hc)
  exact ⟨h.1,h.2,h.2,trivial⟩

theorem circuitComparison : Comparators.CircuitComparison.Target :=
  ⟨fixedInputs,equalityWitness,strictReduction,weakReduction,alwaysOrdered,depthBound,variablesBounded⟩

end LogicLineages.ComputabilityKnowledge.CircuitComparisonProof
