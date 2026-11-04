module
public import LogicLineages.OrdinalComparison.SourceGammaAggregateTargets
public import LogicLineages.OrdinalComparison.SourceGammaCollisionProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceGammaAggregate.Proof
open ParametricSourceEraser ParametricSourceSuccessor SourceGammaCollision SourceGammaCollision.Proof

theorem equal_iff (G : Nat → Nat) {Γ} (ν : OrdinalComponent Γ → Ordinal)
    (p q : OriginalTerm Γ .ground) (x y : Nat) (hp : Scalar G ν p x) (hq : Scalar G ν q y) :
    Equal G ν p q ↔ x=y := by
  obtain ⟨vp,hvp,hep⟩ := hp
  obtain ⟨vq,hvq,heq⟩ := hq
  constructor
  · rintro ⟨wa,wb,hwa,hwb,he⟩
    cases Option.some.inj (hvp.symm.trans hwa)
    cases Option.some.inj (hvq.symm.trans hwb)
    exact Nat.cast_injective (hep.symm.trans (he.trans heq))
  · intro h
    exact ⟨vp,vq,hvp,hvq,hep.trans ((congrArg (fun n : Nat => (n : Ordinal)) h).trans heq.symm)⟩

theorem scalar_zero (G : Nat → Nat) (Γ : List Ty) (ν : OrdinalComponent Γ → Ordinal) :
    Scalar G ν (.zeroC : OriginalTerm Γ .ground) 1 := by
  refine ⟨fun _ => .one,rfl,?_⟩
  simp [denoteWith]

theorem equationCalibration : Targets.EquationCalibration :=
  ⟨fun G _ ν p q x y hp hq => equal_iff G ν p q x y hp hq,scalar_zero⟩

theorem combine_numeric (b a a' c c' : Nat) (ha : a' ≤ a) (hc : c' ≤ c) :
    g b (3*a'+c'+2) ≤ g b (3*a+c+2) ∧
    (g b (3*a+c+2)=g b (3*a'+c'+2) ↔ a=a' ∧ c=c') ∧
    (¬ (a=a' ∧ c=c') → 2 ≤ g b (3*a+c+2)-g b (3*a'+c'+2)) := by
  refine ⟨(g_strictMono b).monotone (by omega),?_,?_⟩
  · constructor
    · intro h
      have := (g_strictMono b).injective h
      omega
    · rintro ⟨rfl,rfl⟩
      rfl
  · intro h
    have hn : 3*a'+c'+2<3*a+c+2 := by omega
    have hg := g_four_lt b _ _ hn
    have hp := g_positive b (3*a'+c'+2)
    omega
end LogicLineages.OrdinalComparison.Source.SourceGammaAggregate.Proof
