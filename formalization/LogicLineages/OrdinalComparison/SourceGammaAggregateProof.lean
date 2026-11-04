module
public import LogicLineages.OrdinalComparison.SourceGammaAggregateNumericProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceGammaAggregate.Proof
open ParametricSourceEraser SourceGammaCollision
open SourceAggregateCompletion

theorem all_equal_cons (b : Nat) {Γ} (ν : OrdinalComponent Γ → Ordinal)
    (p q : OriginalTerm Γ .ground) (es : List (OriginalTerm Γ .ground × OriginalTerm Γ .ground)) :
    SourceGammaAggregate.AllEqual b ν ((p,q)::es) ↔
      Equal (SourceMachineControlNonperiodicity.gamma b) ν p q ∧ SourceGammaAggregate.AllEqual b ν es := by
  constructor
  · intro h
    exact ⟨h (p,q) (by simp),fun e he => h e (List.mem_cons_of_mem _ he)⟩
  · rintro ⟨h,ht⟩ e he
    rcases List.mem_cons.mp he with rfl | he
    · exact h
    · exact ht e he

theorem finiteAggregate : Targets.FiniteAggregate := by
  intro b Γ ν es
  induction es with
  | nil =>
      intro _
      have hz := scalar_zero (SourceMachineControlNonperiodicity.gamma b) Γ ν
      refine ⟨1,1,hz,hz,le_rfl,?_,?_⟩
      · simp [SourceGammaAggregate.AllEqual]
      · simp [SourceGammaAggregate.AllEqual]
  | cons e es ih =>
      rcases e with ⟨p,q⟩
      intro hf
      obtain ⟨x,y,hp,hq⟩ := hf (p,q) (List.mem_cons_self)
      have ht : FiniteLeaves b ν es := fun e he => hf e (List.mem_cons_of_mem _ he)
      obtain ⟨l,r,hl,hr,hord,heq,hgap⟩ := ih ht
      have hd := SourceGammaCollision.Proof.actualSourceCollision b Γ ν p q x y hp hq
      have hnum := SourceGammaCollision.Proof.numericCollision b x y
      have hc := combine_numeric b (leftValue b x y) (rightValue b x y) l r hnum.1 hord
      have hL := SourceGammaCollision.Proof.eraser_scalar b ν _ _ _ _ hd.1 hl
      have hR := SourceGammaCollision.Proof.eraser_scalar b ν _ _ _ _ hd.2.1 hr
      have he : (leftValue b x y=rightValue b x y ∧ l=r) ↔
          SourceGammaAggregate.AllEqual b ν ((p,q)::es) := by
        rw [all_equal_cons]
        exact and_congr (hnum.2.1.trans (equal_iff _ ν p q x y hp hq).symm) heq
      refine ⟨_,_,hL,hR,hc.1,hc.2.1.trans he,?_⟩
      intro h
      exact hc.2.2 (fun hh => h (he.mp hh))

theorem naturalEquationAggregate : Targets.NaturalEquationAggregate := by
  intro b Γ ρ es hf
  exact finiteAggregate b Γ (fun c => ((ρ c+1 : Nat) : Ordinal)) es hf
end LogicLineages.OrdinalComparison.Source.SourceGammaAggregate.Proof
