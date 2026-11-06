module
public import LogicLineages.OrdinalComparison.WordGuardCompletion.Targets
public import LogicLineages.OrdinalComparison.CounterResidualDivergenceLowerProof
public import LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.FocusedProcessBridgeProof
public import LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.FocusedControlProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.WordGuardCompletion.Proof
open PolynomialGraphCompletion KernelSourceCompletion KernelSourceCompletion.UniformCompletion

/-- The source counter itself dominates its input on an explicit genuine tail.
This uses the quadratic count, not a hypothesized growth oracle. -/
theorem sourceCount_lower (d c t : Nat) (hd : 2 ≤ d) (ht : c+d+1 ≤ t) :
    t ≤ sourceCount d c t := by
  have hb := Focused.sourceProcessBridge d c t (by omega) ht
  have hc := CounterResidualDivergence.Proof.actualFiniteDegreeLowerCount.1 d c t hd ht
  have hq := CounterLeaderExpansion.Proof.quadraticCount c t (by omega)
  have hg := Focused.four_mul_lt_Phi t
  change actualSuffixKernelCount (Ordinal.omega0 ^ (2 : Ordinal)) c t ≤
    actualSuffixKernelCount (Ordinal.omega0 ^ (d : Ordinal)) c t at hc
  rw [hq] at hc
  rw [hb.1]
  omega

theorem letterTailCorrect : Targets.LetterTailCorrect := by
  intro D a t ha ht
  rcases a with ⟨tag,d,c,j⟩
  change c+d+j.natAbs+4 ≤ t at ht
  have hj : -(j.natAbs : Int) ≤ j := by cases j <;> simp <;> omega
  have hPhi := self_lt_Phi t
  have hfour := Focused.four_mul_lt_Phi t
  by_cases h0 : tag = 0
  · subst tag
    have hnonneg : 0 ≤ (t : Int)+j := by omega
    change (0 ≤ (t : Int)+j) ∧ t ≤ ((t : Int)+j).toNat+j.natAbs
    exact ⟨hnonneg,by omega⟩
  · by_cases h1 : tag = 1
    · subst tag
      change True ∧ t ≤ Phi t+j.natAbs
      exact ⟨trivial, by omega⟩
    · by_cases h2 : tag = 2
      · subst tag
        have hpos : (0 : Int) < ((Phi t/2 : Nat) : Int)+j+1 := by omega
        have hiter := iterate_self_le (fun x => (self_lt_Phi x).le)
          ((((Phi t/2 : Nat) : Int)+j+1).toNat) t
        change ((0 : Int) < ((Phi t/2 : Nat) : Int)+j+1) ∧
          t ≤ rawQuadraticShift j t+j.natAbs
        refine ⟨hpos, ?_⟩
        change t ≤ (Phi^[(((Phi t/2 : Nat) : Int)+j+1).toNat]) t+j.natAbs
        omega
      · have htag : tag = 3 ∨ tag = 4 := by
          have hnot : ¬ tag ≤ 2 := by omega
          have hh : (tag = 3 ∨ tag = 4) ∧ 3 ≤ d ∧ d ≤ D := by
            simpa only [LetterAllowed, hnot, if_false] using ha
          exact hh.1
        have hd : 3 ≤ d := by
          have hnot : ¬ tag ≤ 2 := by omega
          have hh : (tag = 3 ∨ tag = 4) ∧ 3 ≤ d ∧ d ≤ D := by
            simpa only [LetterAllowed, hnot, if_false] using ha
          exact hh.2.1
        have hc : c ≤ Phi t := by omega
        have hcount := sourceCount_lower d c t (by omega) (by omega)
        rcases htag with h3 | h4
        · subst tag
          have hdepth : 0 < sourceSignedDepth d c j t := by
            unfold sourceSignedDepth
            omega
          have hiter := iterate_self_le (fun x => (self_lt_Phi x).le)
            ((sourceSignedDepth d c j t).toNat) t
          change (c ≤ Phi t ∧ 0 < sourceSignedDepth d c j t) ∧
            t ≤ sourceSignedValue d c j t+j.natAbs
          refine ⟨⟨hc,hdepth⟩,?_⟩
          unfold sourceSignedValue
          omega
        · subst tag
          change ((4 : Nat) = 4 ∧ c ≤ Phi t) ∧ t ≤ sourceCount d c t+j.natAbs
          exact ⟨⟨rfl,hc⟩,by omega⟩

end LogicLineages.OrdinalComparison.WordGuardCompletion.Proof
