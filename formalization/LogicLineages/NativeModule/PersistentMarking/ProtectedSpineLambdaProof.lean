module

public import LogicLineages.NativeModule.PersistentMarking.ProtectedSpineLambdaCallProof
public import LogicLineages.NativeModule.PersistentMarking.ProtectedSpineLambdaFieldProof

@[expose] public section

namespace LogicLineages.PersistentMarking.ProtectedSpineLambdaProof
open Spine DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics
open ProtectedSpineInterpreterCore ProtectedSpineLaws ProtectedSpineLambdaCallProof

theorem applicationEq (E : Environment) (σ ρ : Ty) (body : Evaluation) (Γ Δ : Context)
    (a : Assignments) (ds : List Ty) (τ : Ty) (xs : List Code) :
    (valueAt (lambdaEvaluation E σ ρ body) Γ a).application Δ ds τ xs =
      nonemptyAt E (lambdaEvaluation E σ ρ body) Δ (a.restrict E Γ Δ) 0 ds τ xs := by
  cases ds <;> cases xs <;> rfl

theorem tupleRefl (E : Environment) (Γ : Context) (ds : List Ty) (xs : List Code)
    (hw : WellFormed E.types E.ports Γ) (hx : TupleValues E Γ ds xs) : ValuesLE E Γ ds xs xs := by
  intro i σ x y hσ hx' hy
  cases hx'.symm.trans hy
  exact (HereditaryPartialOrderProof.partialOrder E σ Γ hw).1 x (hx.2 i σ x hσ hx')

theorem laws (E : Environment) (σ ρ : Ty) (body : Evaluation)
    (hσ : σ ∈ E.types) (hl : EvaluationLaws E ρ body) :
    EvaluationLaws E (.arrow σ ρ) (lambdaEvaluation E σ ρ body) := by
  refine ⟨?_,?_,?_,callValid E σ ρ body hl,callNatural E σ ρ body hl,callOrder E σ ρ body hl⟩
  · intro Γ a ha
    refine ⟨?_,?_,?_⟩
    · intro Δ hd he ds τ hp xs hx
      rw [applicationEq]
      exact callValid E σ ρ body hl Δ _ 0 ds τ xs (ProtectedSpineInputProof.restrictValid E Γ Δ a ha hd he) hp hx
    · intro Δ hd he ds τ hp xs ys hx hy hxy
      rw [applicationEq,applicationEq]
      have hΔ := ProtectedSpineInputProof.restrictValid E Γ Δ a ha hd he
      exact callOrder E σ ρ body hl Δ _ _ 0 ds τ xs ys hΔ hΔ
        (ProtectedSpineInputProof.reflexive E Δ _ hΔ) hp hx hy hxy
    · intro Δ Θ hd ht he hf ds τ hp xs hx
      rw [applicationEq,applicationEq]
      have hc := ProtectedSpineInputProof.restrictCompose E Γ Δ Θ a ha hd ht he hf
      rw [← hc]
      exact callNatural E σ ρ body hl Δ Θ _ 0 ds τ xs
        (ProtectedSpineInputProof.restrictValid E Γ Δ a ha hd he) ht hf hp hx
  · intro Γ Δ a ha hd he Θ ht hf
    refine ⟨rfl,?_,?_⟩
    · intro t _
      exact ⟨ProtectedSpineLambdaFieldProof.natural E σ body Γ Δ Θ a ha hd ht he hf hσ false t,
        ProtectedSpineLambdaFieldProof.natural E σ body Γ Δ Θ a ha hd ht he hf hσ true t⟩
    · intro ds τ _ xs _
      rw [applicationEq,applicationEq,ProtectedSpineInputProof.restrictCompose E Γ Δ Θ a ha hd ht he hf]
  · intro Γ a b ha hb hab Δ hd he
    refine ⟨fun _ => rfl,?_,?_⟩
    · intro t ht
      exact ⟨ProtectedSpineLambdaFieldProof.monotone E σ ρ body hl Γ Δ a b ha hb hab hd he hσ false t ht,
        ProtectedSpineLambdaFieldProof.monotone E σ ρ body hl Γ Δ a b ha hb hab hd he hσ true t ht⟩
    · intro ds τ hp xs hx
      rw [applicationEq,applicationEq]
      exact callOrder E σ ρ body hl Δ _ _ 0 ds τ xs xs
        (ProtectedSpineInputProof.restrictValid E Γ Δ a ha hd he)
        (ProtectedSpineInputProof.restrictValid E Γ Δ b hb hd he)
        (ProtectedSpineInputProof.restrictOrder E Γ Δ a b ha hb hab hd he) hp hx hx (tupleRefl E Δ ds xs hd hx)

end LogicLineages.PersistentMarking.ProtectedSpineLambdaProof
