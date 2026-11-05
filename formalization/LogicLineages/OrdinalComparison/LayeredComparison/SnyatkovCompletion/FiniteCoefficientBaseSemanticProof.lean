module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteCoefficientBaseTargets
public import LogicLineages.OrdinalComparison.ActualFiniteHead
public import LogicLineages.OrdinalComparison.ParametricFiniteCollapseArgumentArithmeticProof
public import LogicLineages.OrdinalComparison.NaturalProductInterpretation
public import LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteCoefficientBaseProof
open FiniteCoefficientBase Source Source.ForwardTranslation CommonLayerSyntax
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof

theorem actualCoefficient : FiniteCoefficientBaseTargets.ActualCoefficient := by
  intro c
  induction c with
  | one => intro k hk; cases Option.some.inj hk; exact ⟨by decide, by simp [ClosedPositive.evaluate]⟩
  | omega => intro k hk; simp [coefficient] at hk
  | add a b iha ihb =>
    intro k hk
    obtain ⟨x, hx, y, hy, rfl⟩ : ∃ x, coefficient a = some x ∧ ∃ y, coefficient b = some y ∧ x+y=k := by
      simpa only [coefficient, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] using hk
    obtain ⟨hxp, hxv⟩ := iha x hx
    obtain ⟨hyp, hyv⟩ := ihb y hy
    refine ⟨by omega, ?_⟩
    change (naturalSum a.evaluate b.evaluate).1.repr = _
    rw [naturalSumDenotation, hxv, hyv]
    exact naturalSum_finite x y
  | emul a b iha ihb =>
    intro k hk
    obtain ⟨x, hx, y, hy, rfl⟩ : ∃ x, coefficient a = some x ∧ ∃ y, coefficient b = some y ∧ 2^x*y=k := by
      simpa only [coefficient, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] using hk
    obtain ⟨hxp, hxv⟩ := iha x hx
    obtain ⟨hyp, hyv⟩ := ihb y hy
    refine ⟨Nat.mul_pos (Nat.pow_pos (by decide)) hyp, ?_⟩
    change (naturalProduct (NONote.opow ⟨ONote.ofNat 2, _⟩ a.evaluate) b.evaluate).1.repr = _
    rw [naturalProductDenotation]
    change ordinalNaturalProduct ((ONote.ofNat 2) ^ a.evaluate.1).repr b.evaluate.1.repr = _
    letI : ONote.NF a.evaluate.1 := a.evaluate.2
    rw [ONote.repr_opow, ONote.repr_ofNat, hxv, hyv]
    simp only [Nat.cast_ofNat]
    rw [(finiteArithmetic x 0).2.2]
    exact naturalProduct_finite (2^x) y

theorem iterate_value (k : Nat) (t : BaseTerm) (ν : Nat → Nat) :
    (iteratePhi k t).value ν = (Phi^[k]) (t.value ν) := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [iteratePhi, BaseTerm.value, ih] using (Function.iterate_succ_apply' Phi k (t.value ν)).symm

theorem iterate_variables (k : Nat) (t : BaseTerm) : (iteratePhi k t).variables = t.variables := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih

theorem exactExpansion : FiniteCoefficientBaseTargets.ExactExpansion := by
  intro k t
  constructor
  · intro ν
    simp only [expand, BaseTerm.value, iterate_value]
    rw [actualFiniteHeadCollapse k (t.value ν)]
    congr 2
    omega
  · simp only [expand, BaseTerm.variables, iterate_variables, List.append_nil]

theorem actualScalar : FiniteCoefficientBaseTargets.ActualScalar := by
  intro ι index s
  induction s with
  | one => intro t ht; cases Option.some.inj ht; exact ⟨fun _ => rfl, rfl⟩
  | var i => intro t ht; cases Option.some.inj ht; exact ⟨fun _ => rfl, rfl⟩
  | add a b iha ihb =>
    intro t ht
    obtain ⟨x, hx, y, hy, rfl⟩ : ∃ x, compile index a = some x ∧ ∃ y, compile index b = some y ∧ BaseTerm.add x y=t := by
      simpa only [compile, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] using ht
    obtain ⟨hxv, hxs⟩ := iha x hx
    obtain ⟨hyv, hys⟩ := ihb y hy
    exact ⟨fun ν => congrArg₂ Nat.add (hxv ν) (hyv ν), by simp only [BaseTerm.variables, support, hxs, hys]⟩
  | shift c a ih =>
    intro t ht
    obtain ⟨k, hk, x, hx, rfl⟩ : ∃ k, coefficient c = some k ∧ ∃ x, compile index a = some x ∧ expand k x=t := by
      simpa only [compile, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] using ht
    obtain ⟨hxv, hxs⟩ := ih x hx
    refine ⟨?_, (exactExpansion k x).2.trans hxs⟩
    intro ν
    rw [(exactExpansion k x).1 ν, hxv ν]
    change actualCollapse _ = actualCollapse (ordinalNaturalProduct Ordinal.omega0 c.evaluate.1.repr + _)
    rw [(actualCoefficient c k hk).2, Source.ParametricFiniteCollapseArgument.Proof.naturalProduct_omega_finite]

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteCoefficientBaseProof
