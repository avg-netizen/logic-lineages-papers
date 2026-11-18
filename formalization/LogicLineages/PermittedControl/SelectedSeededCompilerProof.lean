module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.SeededBoundProof
public import LogicLineages.PermittedControl.SelectedSeededCompilerTargets
public import LogicLineages.PermittedControl.SelectedOmegaSeedProof
public import LogicLineages.PermittedControl.SelectedPairCompilerAlgebraProof
@[expose] public section
namespace LogicLineages.PermittedControl.SelectedSeededCompiler.Proof
open OrdinalComparison Source SelectedSourceDomain SignedPair SignedPair.Proof
open Source.FunctionalHardnessCompletion
open SeededCompiler (subtractSeed linearMeaning)
open SelectedPairCompiler (difference)

/-- All scale arithmetic comes from the accepted compiler combinator clauses;
only the additional closed-seed variable branch is new. -/
theorem compiler_difference (ctrl : Nat → Nat) (B : Nat) (hc : SelectedWithThreshold ctrl B)
    (policy : AdmissibleSum.Policy) {n : Nat} (d : Expression (n+1))
    (ρ : AdmissibleSubstitution ctrl (Context n)) :
    difference ctrl policy ρ (SeededCompiler.compile d).pair=(2^(SeededCompiler.compile d).exponent : Int) • meaning (seededInputs ctrl ρ) d := by
  induction d with
  | unit => exact SelectedPairCompiler.Proof.unit_difference ctrl B hc policy ρ
  | var i =>
      unfold SeededCompiler.compile
      split
      · rename_i h
        simpa only [seededInputs,meaning,dif_pos h] using SelectedPairCompiler.Proof.variable_difference ctrl B hc policy ρ ⟨i.val,h⟩
      · rename_i h
        simpa only [seededInputs,meaning,dif_neg h] using (SelectedOmegaSeed.Proof.actualScaledPair ctrl B hc _ policy ρ).2.2.2
  | neg a ha =>
      change signedCNF (SelectedHardness.value1 ctrl policy ρ (SeededCompiler.compile a).pair.2)-
        signedCNF (SelectedHardness.value1 ctrl policy ρ (SeededCompiler.compile a).pair.1)=_
      rw [←neg_sub]
      change -difference ctrl policy ρ (SeededCompiler.compile a).pair=_
      rw [ha]
      exact (smul_neg _ _).symm
  | shift a ha =>
      change difference ctrl policy ρ (liftOmega (SeededCompiler.compile a).pair.1,liftOmega (SeededCompiler.compile a).pair.2)=_
      rw [SelectedPairCompiler.Proof.omega_difference ctrl B hc policy,ha,shift_smul,smul_smul]
      change (2*2^(SeededCompiler.compile a).exponent : Int) • omegaShift (meaning (seededInputs ctrl ρ) a)=
        (2^((SeededCompiler.compile a).exponent+1) : Int) • omegaShift (meaning (seededInputs ctrl ρ) a)
      rw [pow_succ']
  | add a b ha hb =>
      let K := max (SeededCompiler.compile a).exponent (SeededCompiler.compile b).exponent
      change difference ctrl policy ρ (join (pad (K-(SeededCompiler.compile a).exponent) (SeededCompiler.compile a).pair)
        (pad (K-(SeededCompiler.compile b).exponent) (SeededCompiler.compile b).pair))=
        (2^(K+9) : Int) • (meaning (seededInputs ctrl ρ) a+meaning (seededInputs ctrl ρ) b)
      rw [SelectedPairCompiler.Proof.join_difference ctrl B hc policy,SelectedPairCompiler.Proof.pad_align ctrl B hc policy ρ _ _ K (Nat.le_max_left _ _) _ ha,
        SelectedPairCompiler.Proof.pad_align ctrl B hc policy ρ _ _ K (Nat.le_max_right _ _) _ hb,←smul_add,smul_smul]
      have he : (8*2^(K+6) : Int)=2^(K+9) := by
        rw [show (8 : Int)=2^3 by norm_num,←pow_add]
        congr 1
        omega
      rw [he]

theorem actualCompiler : SelectedSeededCompilerTargets.ActualCompiler := by
  intro ctrl K hc n d
  refine ⟨(SeededCompiler.Proof.compiler_bound d).1,(SeededCompiler.Proof.compiler_bound d).2,?_⟩
  intro policy ρ
  refine ⟨?_,compiler_difference ctrl K hc policy d ρ⟩
  obtain ⟨av,ha,_,_⟩ := SelectedFunctionalDetector.Proof.values_assignment ctrl K hc policy ρ (SeededCompiler.compile d).pair.1
  obtain ⟨bv,hb,_,_⟩ := SelectedFunctionalDetector.Proof.values_assignment ctrl K hc policy ρ (SeededCompiler.compile d).pair.2
  refine ⟨av,bv,ha,hb,?_,?_⟩
  · rw [←SelectedHardnessCoordinatesProof.value1_of_assignment ctrl policy ρ _ _ ha]
    exact (SelectedFunctionalDetector.Proof.values_facts ctrl K hc policy ρ _).2.1
  · rw [←SelectedHardnessCoordinatesProof.value1_of_assignment ctrl policy ρ _ _ hb]
    exact (SelectedFunctionalDetector.Proof.values_facts ctrl K hc policy ρ _).2.1

theorem exactSeedSubstitution : SelectedSeededCompilerTargets.SeedSubstitution := by
  intro n x seed d
  induction d with
  | unit => rfl
  | var i => simp [subtractSeed,meaning,linearMeaning,sub_eq_add_neg]
  | add a b ha hb => simpa only [subtractSeed,meaning,linearMeaning,ha,hb]
  | neg a ha => simpa only [subtractSeed,meaning,linearMeaning,ha]
  | shift a ha => simpa only [subtractSeed,meaning,linearMeaning,ha]

theorem seededInputs_eq_lastCases (ctrl : Nat → Nat) {n : Nat} (ρ : AdmissibleSubstitution ctrl (Context n)) :
    seededInputs ctrl ρ=Fin.lastCases (SelectedOmegaSeed.omega ctrl) (SelectedPairCompiler.inputs ctrl ρ) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [seededInputs]
  · simp [seededInputs,j.isLt]

end LogicLineages.PermittedControl.SelectedSeededCompiler.Proof
