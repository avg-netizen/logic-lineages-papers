module
public import LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.QuantitativeBudgetProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.Proof

/-- The quadratic formula is used only at genuine child inputs. -/
private theorem source_quadratic_count (c t : Nat) (ht : c+3 ≤ t) :
    sourceCount 2 c t = Phi t/2-(c+1)/2+1 := by
  have hbridge := Focused.sourceProcessBridge 2 c t (by omega) (by omega)
  rw [hbridge.1]
  exact Focused.actualOmegaSquaredSuffixCount c t ht

private theorem source_quadratic_mass (c e t : Nat)
    (hc : c+3 ≤ t) (he : e+3 ≤ t) (hceil : (c+1)/2 < (e+1)/2) :
    sourceValue 2 e t < sourceValue 2 c t := by
  have hm : StrictMono (fun n : Nat => (Phi^[n]) t) :=
    Phi_strictMono.strictMono_iterate_of_lt_map (self_lt_Phi t)
  change (Phi^[sourceCount 2 e t]) t < (Phi^[sourceCount 2 c t]) t
  apply hm
  rw [source_quadratic_count e t he,source_quadratic_count c t hc]
  have hg := Focused.four_mul_lt_Phi t
  omega

/-- A genuine integer gap between quadratic child inputs pays the required
extra iterations. The bound is on the actual smaller child input. -/
private theorem source_quadratic_amplify (c e R w v : Nat)
    (hwv : w < v) (hb : c+e+R+4 ≤ w) :
    (Phi^[R]) (sourceValue 2 e w) < sourceValue 2 c v := by
  have he : e+3 ≤ w := by omega
  have hc : c+3 ≤ v := by omega
  have hg := Focused.four_mul_lt_Phi w
  have hs := four_mul_Phi_lt_succ w
  have hv : Phi (w+1) ≤ Phi v := Phi_strictMono.monotone (by omega)
  have hcount : R+sourceCount 2 e w ≤ sourceCount 2 c v := by
    rw [source_quadratic_count e w he,source_quadratic_count c v hc]
    omega
  change (Phi^[R]) ((Phi^[sourceCount 2 e w]) w) <
    (Phi^[sourceCount 2 c v]) v
  rw [← Function.iterate_add_apply]
  exact ((Phi_strictMono.iterate (R+sourceCount 2 e w)) hwv).trans_le
    (iterate_index_mono (fun x => (self_lt_Phi x).le) v hcount)

/-- When adjacent masses have different quadratic ceilings, one aligned
block is already strict. No congruence of the original first budget is needed. -/
private theorem cubic_ceiling_step (c t : Nat) (hb : c+4 ≤ Phi t)
    (hceil : (c+1)/2 < (c+2)/2) :
    sourceValue 3 (c+1) t < sourceValue 3 c t := by
  let U := sourceValue 3 (c+3) t
  let V := sourceValue 3 (c+4) t
  have hlower : Phi t ≤ V := source_value_lower 3 (c+4) t (by omega) hb
  have hinner : V ≤ U :=
    (Focused.sourceInputMassOrder 3 (c+3) (c+4) t t (by omega)
      (by omega) le_rfl hb).2.2.1
  have hquad : sourceValue 2 (c+1) V < sourceValue 2 c V :=
    source_quadratic_mass c (c+1) V (by omega) (by omega) (by omega)
  have hdom : c ≤ Phi V := by have hg := self_lt_Phi V; omega
  have hmono : sourceValue 2 c V ≤ sourceValue 2 c U :=
    (Focused.sourceInputMassOrder 2 c c V U (by omega) le_rfl hinner hdom).2.2.1
  rw [sourceBlock_step 1 (c+1) t (by omega),sourceBlock_step 1 c t (by omega)]
  change sourceValue 2 (c+1) V < sourceValue 2 c U
  exact hquad.trans_le hmono

/-- Either the current ceiling or the one three masses later is strict.
Two aligned blocks therefore separate every adjacent cubic mass. -/
private theorem cubic_adjacent_mass (c t : Nat) (hb : c+7 ≤ Phi t) :
    sourceValue 3 (c+1) t < sourceValue 3 c t := by
  by_cases hceil : (c+1)/2 < (c+2)/2
  · exact cubic_ceiling_step c t (by omega) hceil
  · have hshift : ((c+3)+1)/2 < ((c+3)+2)/2 := by omega
    have hinner := cubic_ceiling_step (c+3) t (by omega) hshift
    let U := sourceValue 3 (c+3) t
    let V := sourceValue 3 (c+4) t
    have hVU : V < U := by simpa only [Nat.add_assoc] using hinner
    have hlower : Phi t ≤ V := source_value_lower 3 (c+4) t (by omega) (by omega)
    have hdom : c+1 ≤ Phi V := by have hg := self_lt_Phi V; omega
    have hquad := (Focused.sourceInputMassOrder 2 c (c+1) V U (by omega)
      (by omega) hVU.le hdom).2.2.2 hVU
    rw [sourceBlock_step 1 (c+1) t (by omega),sourceBlock_step 1 c t (by omega)]
    change sourceValue 2 (c+1) V < sourceValue 2 c U
    exact hquad

private theorem cubic_strict_mass (c e t : Nat) (hce : c < e)
    (hc : c+7 ≤ Phi t) (he : e ≤ Phi t) :
    sourceValue 3 e t < sourceValue 3 c t := by
  have hmono := (Focused.sourceInputMassOrder 3 (c+1) e t t (by omega)
    (by omega) le_rfl he).2.2.1
  exact hmono.trans_lt (cubic_adjacent_mass c t hc)

/-- Three aligned quadratic blocks suffice: two create the strict mass gap
and the outer block amplifies it to the requested iteration allowance. -/
theorem cubicUnsignedSeparation : Targets.CubicUnsignedSeparation := by
  intro c e R t _ hb
  have hsmall : c+e+R+10 ≤ Phi t := by omega
  have hlower : Phi t ≤ sourceValue 3 (e+3) t :=
    source_value_lower 3 (e+3) t (by omega) (by omega)
  have hnext : Phi t ≤ Phi (t+1) := Phi_strictMono.monotone (by omega)
  constructor
  · have hinner := source_cross_value 3 (c+3) (e+3) t (by omega)
    have hquad := source_quadratic_amplify c e R
      (sourceValue 3 (e+3) t) (sourceValue 3 (c+3) (t+1)) hinner (by omega)
    rw [sourceBlock_step 1 e t (by omega),sourceBlock_step 1 c (t+1) (by omega)]
    exact hquad
  · intro hce
    have hinner := cubic_strict_mass (c+3) (e+3) t (by omega) (by omega) (by omega)
    have hquad := source_quadratic_amplify c e R
      (sourceValue 3 (e+3) t) (sourceValue 3 (c+3) t) hinner (by omega)
    rw [sourceBlock_step 1 e t (by omega),sourceBlock_step 1 c t (by omega)]
    exact hquad

end LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.Proof
