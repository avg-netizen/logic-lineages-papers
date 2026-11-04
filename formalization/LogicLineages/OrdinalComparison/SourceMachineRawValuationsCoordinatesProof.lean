module
public import LogicLineages.OrdinalComparison.SourceMachineRawValuationsTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceMachineRawValuations.Proof
open ExistentialPlan PrimitiveLowering

theorem compile_ground {Γ} (q : Plan Γ) : AllGround Γ → AllGround (compile q).context := by
  induction q with
  | done => exact id
  | equation a b q ih => exact ih
  | gate g q ih =>
    intro h σ hs
    change σ ∈ List.replicate 9 Ty.ground ++ (compile q).context at hs
    rcases List.mem_append.mp hs with hs | hs
    · exact (List.mem_replicate.mp hs).2
    · exact ih h σ hs
  | existsGround q ih =>
    intro h
    apply ih
    intro σ hs
    rcases List.mem_cons.mp hs with hs | hs
    · exact hs
    · exact h σ hs

theorem groundContexts : Targets.GroundContexts := by
  refine ⟨fun _ q => compile_ground q,?_⟩
  intro b e
  apply compile_ground
  intro σ hs
  exact (List.mem_replicate.mp hs).2

theorem variable_ground {Γ σ} (h : AllGround Γ) (x : Variable Γ σ) : σ=Ty.ground := by
  induction x with
  | here => exact h _ (List.mem_cons_self)
  | there x ih =>
    apply ih
    intro τ ht
    exact h τ (List.mem_cons_of_mem _ ht)

theorem positiveCoordinateEquivalence : Targets.PositiveCoordinateEquivalence := by
  intro Γ hΓ
  refine ⟨fun ρ c => Nat.zero_lt_succ _,?_⟩
  intro ν hp
  let ρ : Variable Γ .ground → Nat := fun x => ν ⟨.ground,x,0⟩-1
  refine ⟨ρ,?_,?_⟩
  · intro c
    rcases c with ⟨σ,x,j⟩
    have hs := variable_ground hΓ x
    cases hs
    have hj : j=0 := Fin.eq_zero j
    subst j
    change ν ⟨.ground,x,0⟩ = (ν ⟨.ground,x,0⟩-1)+1
    have hh := hp ⟨.ground,x,0⟩
    omega
  · intro μ hμ
    funext x
    have hh := hμ ⟨.ground,x,0⟩
    change ν ⟨.ground,x,0⟩=μ x+1 at hh
    change μ x=ν ⟨.ground,x,0⟩-1
    omega
end LogicLineages.OrdinalComparison.Source.SourceMachineRawValuations.Proof
