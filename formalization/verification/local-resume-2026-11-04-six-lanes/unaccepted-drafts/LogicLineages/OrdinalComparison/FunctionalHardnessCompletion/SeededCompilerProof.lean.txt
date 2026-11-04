module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.SeededBoundProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.SeededCompiler.Proof
open OriginalDomain SignedPair SignedPair.Proof

/-- All scale arithmetic comes from the accepted compiler combinator clauses;
only the additional closed-seed variable branch is new. -/
theorem compiler_difference {n : Nat} (d : Expression (n+1))
    (ρ : AdmissibleSubstitution (Context n)) :
    difference ρ (compile d).pair=(2^(compile d).exponent : Int) • meaning (seededInputs ρ) d := by
  induction d with
  | unit => exact unit_difference ρ
  | var i =>
      unfold compile
      split
      · rename_i h
        simpa only [seededInputs,meaning,dif_pos h] using variable_difference ρ ⟨i.val,h⟩
      · rename_i h
        simpa only [seededInputs,meaning,dif_neg h] using (OmegaSeed.Proof.actualScaledPair _ ρ).2.2
  | neg a ha =>
      change signedCNF (FunctionalDetector.Proof.value1 ρ (compile a).pair.2)-
        signedCNF (FunctionalDetector.Proof.value1 ρ (compile a).pair.1)=_
      rw [←neg_sub]
      change -difference ρ (compile a).pair=_
      rw [ha]
      exact (smul_neg _ _).symm
  | shift a ha =>
      change difference ρ (liftOmega (compile a).pair.1,liftOmega (compile a).pair.2)=_
      rw [omega_difference,ha,shift_smul,smul_smul]
      change (2*2^(compile a).exponent : Int) • omegaShift (meaning (seededInputs ρ) a)=
        (2^((compile a).exponent+1) : Int) • omegaShift (meaning (seededInputs ρ) a)
      rw [pow_succ']
  | add a b ha hb =>
      let K := max (compile a).exponent (compile b).exponent
      change difference ρ (join (pad (K-(compile a).exponent) (compile a).pair)
        (pad (K-(compile b).exponent) (compile b).pair))=
        (2^(K+9) : Int) • (meaning (seededInputs ρ) a+meaning (seededInputs ρ) b)
      rw [join_difference,pad_align ρ _ _ K (Nat.le_max_left _ _) _ ha,
        pad_align ρ _ _ K (Nat.le_max_right _ _) _ hb,←smul_add,smul_smul]
      have he : (8*2^(K+6) : Int)=2^(K+9) := by
        rw [show (8 : Int)=2^3 by norm_num,←pow_add]
        congr 1
        omega
      rw [he]

theorem exactSeededCompiler : Targets.ExactSeededCompiler := by
  intro n d
  exact ⟨(compiler_bound d).1,(compiler_bound d).2,compiler_difference d⟩

theorem exactSeedSubstitution : Targets.ExactSeedSubstitution := by
  intro n x seed d
  induction d with
  | unit => rfl
  | var i => simp [subtractSeed,meaning,linearMeaning,sub_eq_add_neg]
  | add a b ha hb => simpa only [subtractSeed,meaning,linearMeaning,ha,hb]
  | neg a ha => simpa only [subtractSeed,meaning,linearMeaning,ha]
  | shift a ha => simpa only [subtractSeed,meaning,linearMeaning,ha]

theorem seededInputs_eq_lastCases {n : Nat} (ρ : AdmissibleSubstitution (Context n)) :
    seededInputs ρ=Fin.lastCases OmegaSeed.omega (inputs ρ) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [seededInputs]
  · simp [seededInputs,j.isLt]

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.SeededCompiler.Proof
