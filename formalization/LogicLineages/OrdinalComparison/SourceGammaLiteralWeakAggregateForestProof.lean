module
public import LogicLineages.OrdinalComparison.SourceGammaLiteralWeakAggregateTargets
public import LogicLineages.OrdinalComparison.ParametricLiteralWeakWrapperProof
public import LogicLineages.OrdinalComparison.SourceGammaAggregateProof

@[expose] public section

namespace LogicLineages.OrdinalComparison.Source.SourceGammaLiteralWeakAggregate.Proof

open ParametricSourceEraser ParametricLiteralWeakWrapper SourceGammaCollision
open SourceAggregateCompletion

theorem numericGap : Targets.NumericGap := by
  intro b l r
  constructor
  · intro h
    by_contra hn
    have hlt : l + 3 < r + 5 := by omega
    have hh := SourceGammaCollision.Proof.g_strictMono b hlt
    omega
  · intro h
    exact (SourceGammaCollision.Proof.g_strictMono b).monotone (by omega)

theorem weakAt_iff_gap (b : Nat) {Γ : List Ty} (ν : OrdinalComponent Γ → Ordinal)
    (es : List (OriginalTerm Γ .ground × OriginalTerm Γ .ground)) (l r : Nat)
    (hl : Scalar (SourceMachineControlNonperiodicity.gamma b) ν (aggregate es).1 l)
    (hr : Scalar (SourceMachineControlNonperiodicity.gamma b) ν (aggregate es).2 r) :
    WeakAt b ν es ↔ r + 2 ≤ l := by
  have hk : Scalar (SourceMachineControlNonperiodicity.gamma b) ν
      (constantApply (aggregate es).2) (g b (r + 5)) :=
    (ParametricLiteralWeakWrapper.Proof.finiteCoefficientCalibration
      (SourceMachineControlNonperiodicity.gamma b) Γ ν _ r hr).2
  have hi : Scalar (SourceMachineControlNonperiodicity.gamma b) ν
      (identityApply (aggregate es).1) (g b (l + 3)) :=
    (ParametricLiteralWeakWrapper.Proof.finiteCoefficientCalibration
      (SourceMachineControlNonperiodicity.gamma b) Γ ν _ l hl).1
  constructor
  · rintro ⟨k, i, hk', hi', hki⟩
    have hek := ParametricSourceEraser.Proof.scalar_unique
      (SourceMachineControlNonperiodicity.gamma b) ν _ _ _ hk' hk
    have hei := ParametricSourceEraser.Proof.scalar_unique
      (SourceMachineControlNonperiodicity.gamma b) ν _ _ _ hi' hi
    rw [hek, hei] at hki
    exact (numericGap b l r).mp hki
  · intro h
    exact ⟨g b (r + 5), g b (l + 3), hk, hi, (numericGap b l r).mpr h⟩

theorem finite_forest_weak (b : Nat) (Γ : List Ty) (ν : OrdinalComponent Γ → Ordinal)
    (es : List (OriginalTerm Γ .ground × OriginalTerm Γ .ground))
    (hf : SourceGammaAggregate.FiniteLeaves b ν es) :
    WeakAt b ν es ↔ ¬SourceGammaAggregate.AllEqual b ν es := by
  obtain ⟨l, r, hl, hr, hord, heq, hgap⟩ :=
    SourceGammaAggregate.Proof.finiteAggregate b Γ ν es hf
  rw [weakAt_iff_gap b ν es l r hl hr]
  constructor
  · intro h he
    have hh := heq.mpr he
    omega
  · intro h
    have hh := hgap h
    omega

theorem weak_iff_strict (b : Nat) (Γ : List Ty) (ν : OrdinalComponent Γ → Ordinal)
    (es : List (OriginalTerm Γ .ground × OriginalTerm Γ .ground))
    (hf : SourceGammaAggregate.FiniteLeaves b ν es) :
    WeakAt b ν es ↔ ∃ l r : Nat,
      Scalar (SourceMachineControlNonperiodicity.gamma b) ν (aggregate es).1 l ∧
      Scalar (SourceMachineControlNonperiodicity.gamma b) ν (aggregate es).2 r ∧ r < l := by
  obtain ⟨l, r, hl, hr, hord, heq, hgap⟩ :=
    SourceGammaAggregate.Proof.finiteAggregate b Γ ν es hf
  constructor
  · intro hw
    have hh := (weakAt_iff_gap b ν es l r hl hr).mp hw
    exact ⟨l, r, hl, hr, by omega⟩
  · rintro ⟨l', r', hl', hr', hlt⟩
    have hel := ParametricSourceEraser.Proof.scalar_unique
      (SourceMachineControlNonperiodicity.gamma b) ν _ _ _ hl' hl
    have her := ParametricSourceEraser.Proof.scalar_unique
      (SourceMachineControlNonperiodicity.gamma b) ν _ _ _ hr' hr
    rw [hel, her] at hlt
    apply (finite_forest_weak b Γ ν es hf).mpr
    intro he
    have hh := heq.mpr he
    omega

theorem finiteForestWeak : Targets.FiniteForestWeak := by
  refine ⟨finite_forest_weak, ?_⟩
  intro b Γ ν
  have hf : SourceGammaAggregate.FiniteLeaves b ν
      ([] : List (OriginalTerm Γ .ground × OriginalTerm Γ .ground)) := by
    intro e he
    simp at he
  have he : SourceGammaAggregate.AllEqual b ν
      ([] : List (OriginalTerm Γ .ground × OriginalTerm Γ .ground)) := by
    intro e he
    simp at he
  intro hw
  exact ((finite_forest_weak b Γ ν [] hf).mp hw) he

end LogicLineages.OrdinalComparison.Source.SourceGammaLiteralWeakAggregate.Proof
