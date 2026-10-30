module
public import LogicLineages.OrdinalComparison.PositiveUnaryIdentityTargets
public import LogicLineages.OrdinalComparison.PositiveFiniteZerosProof
public import LogicLineages.OrdinalComparison.PositiveNormalFlagProof
public import LogicLineages.OrdinalComparison.ControlComputability

@[expose] public section
namespace LogicLineages.OrdinalComparison

theorem actualPositiveUnaryIdentity : Targets.ActualPositiveUnaryIdentity := by
  have hc : Computable₂ encodedPositiveCounterInput :=
    Primrec.nat_add.to_comp.comp
      (Phi_computable.comp fullActualPositiveFiniteZeros.1) (Computable.const 1)
  refine ⟨positiveNormalFlagComputable, fullActualPositiveFiniteZeros.1, hc, ?_⟩
  intro E F hE hF
  let n := positiveExprEncode E
  let m := positiveExprEncode F
  let k := encodedPositiveZeroBound n m
  let v := encodedPositiveCounterInput n m
  have hz := fullActualPositiveFiniteZeros.2.2 E F hE hF
  have hf := positiveNormalFlagCorrect E F hE hF
  have hv : v=Phi k+1 := rfl
  have hkv : k≤v := by
    have hg := self_lt_Phi k
    omega
  have hpos : 0<v := by omega
  refine ⟨hz.1, hv, hpos, ?_, ?_⟩
  · constructor
    · intro h x _
      exact hz.2.1 (hf.mp h) x
    · intro h
      by_contra hn
      have hne : collectedPositiveNormalize E≠collectedPositiveNormalize F := by
        intro he
        exact hn (hf.mpr he)
      exact (hz.2.2.1 hne).1 v hkv (h v hpos)
  · intro hfalse
    have hne : collectedPositiveNormalize E≠collectedPositiveNormalize F := by
      intro he
      have ht := hf.mpr he
      rw [hfalse] at ht
      cases ht
    exact (hz.2.2.1 hne).1 v hkv

end LogicLineages.OrdinalComparison
