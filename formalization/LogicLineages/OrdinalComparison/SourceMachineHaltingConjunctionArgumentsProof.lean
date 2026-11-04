module
public import LogicLineages.OrdinalComparison.SourceMachineHaltingConjunctionTargets
public import LogicLineages.OrdinalComparison.SourceControlNonperiodicityFibersProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.SourceMachineHaltingConjunction.Proof

theorem coefficient_primitive : Primrec coefficient :=
  (Primrec₂.unpaired'.1 Nat.Primrec.pow).comp (Primrec.const 2) Primrec.id

theorem constant_primitive : Primrec oddConstant :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id) (Primrec.const 5)

theorem argument_primitive : Primrec (fun p : Nat×Nat×Nat => argument p.1 p.2.1 p.2.2) :=
  Primrec.nat_mul.comp (coefficient_primitive.comp (Primrec.fst.comp Primrec.snd))
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.snd.comp Primrec.snd))
      (constant_primitive.comp Primrec.fst))

theorem argument_bounds (b e t : Nat) :
    5 ≤ argument b e t ∧ b < argument b e t ∧ t ≤ argument b e t := by
  have hp : 1 ≤ 2^e := Nat.one_le_pow e 2 (by omega)
  have hm := Nat.mul_le_mul_right (2*t+(2*b+5)) hp
  simp only [one_mul] at hm
  unfold argument coefficient oddConstant
  omega

theorem argument_valuation (b e t : Nat) :
    PerturbedControl.valuationTwo (argument b e t) = e := by
  apply SourceControlNonperiodicity.Proof.valuation_of_exact_power
  · have h := argument_bounds b e t
    omega
  · unfold argument coefficient
    exact dvd_mul_right _ _
  · unfold argument coefficient oddConstant
    rw [pow_succ]
    intro hd
    have hp : 0 < 2^e := pow_pos (by omega) _
    have he : 2 ∣ 2*t+(2*b+5) := (Nat.mul_dvd_mul_iff_left hp).1 hd
    have hm := Nat.mod_eq_zero_of_dvd he
    omega

theorem effectiveArguments : Targets.EffectiveArguments := by
  refine ⟨coefficient_primitive,constant_primitive,argument_primitive,?_⟩
  intro b e t
  have h := argument_bounds b e t
  exact ⟨h.1,h.2.1,h.2.2,argument_valuation b e t⟩
end LogicLineages.OrdinalComparison.SourceMachineHaltingConjunction.Proof
