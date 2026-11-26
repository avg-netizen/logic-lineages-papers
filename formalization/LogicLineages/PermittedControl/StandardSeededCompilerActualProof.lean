module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.SeededBoundProof
public import LogicLineages.PermittedControl.StandardSeededCompilerTargets
public import LogicLineages.PermittedControl.StandardOmegaSeedProof
public import LogicLineages.PermittedControl.StandardPairCompilerAlgebraProof
@[expose] public section
namespace LogicLineages.PermittedControl.StandardSeededCompiler.Proof
open OrdinalComparison Source SelectedSourceDomain SignedPair SignedPair.Proof
open Source.FunctionalHardnessCompletion
open SelectedPairCompiler (difference)
open SelectedSeededCompiler (seededInputs)

/-- Compiler induction rebuilt at the unchanged displayed control. Every scale
clause is the standard-control combinator algebra; the extra variable branch is
the actual closed Omega source pair at Phi. No selected-control theorem is used. -/
theorem compiler_difference (policy : AdmissibleSum.Policy) {n : Nat} (d : Expression (n+1))
    (ρ : AdmissibleSubstitution Phi (Context n)) :
    difference Phi policy ρ (SeededCompiler.compile d).pair=
      (2^(SeededCompiler.compile d).exponent : Int) • meaning (seededInputs Phi ρ) d := by
  induction d with
  | unit => exact StandardPairCompiler.Proof.unit_difference policy ρ
  | var i =>
      unfold SeededCompiler.compile
      split
      · rename_i h
        simpa only [seededInputs,meaning,dif_pos h] using
          StandardPairCompiler.Proof.variable_difference policy ρ ⟨i.val,h⟩
      · rename_i h
        simpa only [seededInputs,meaning,dif_neg h] using
          (StandardOmegaSeed.Proof.actualScaledPair _ policy ρ).2.2.2
  | neg a ha =>
      change signedCNF (SelectedHardness.value1 Phi policy ρ (SeededCompiler.compile a).pair.2)-
        signedCNF (SelectedHardness.value1 Phi policy ρ (SeededCompiler.compile a).pair.1)=_
      rw [←neg_sub]
      change -difference Phi policy ρ (SeededCompiler.compile a).pair=_
      rw [ha]
      exact (smul_neg _ _).symm
  | shift a ha =>
      change difference Phi policy ρ
        (liftOmega (SeededCompiler.compile a).pair.1,liftOmega (SeededCompiler.compile a).pair.2)=_
      rw [StandardPairCompiler.Proof.omega_difference policy,ha,shift_smul,smul_smul]
      change (2*2^(SeededCompiler.compile a).exponent : Int) • omegaShift (meaning (seededInputs Phi ρ) a)=
        (2^((SeededCompiler.compile a).exponent+1) : Int) • omegaShift (meaning (seededInputs Phi ρ) a)
      rw [pow_succ']
  | add a b ha hb =>
      let K := max (SeededCompiler.compile a).exponent (SeededCompiler.compile b).exponent
      change difference Phi policy ρ (join (pad (K-(SeededCompiler.compile a).exponent) (SeededCompiler.compile a).pair)
        (pad (K-(SeededCompiler.compile b).exponent) (SeededCompiler.compile b).pair))=
        (2^(K+9) : Int) • (meaning (seededInputs Phi ρ) a+meaning (seededInputs Phi ρ) b)
      rw [StandardPairCompiler.Proof.join_difference policy,
        StandardPairCompiler.Proof.pad_align policy ρ _ _ K (Nat.le_max_left _ _) _ ha,
        StandardPairCompiler.Proof.pad_align policy ρ _ _ K (Nat.le_max_right _ _) _ hb,←smul_add,smul_smul]
      have he : (8*2^(K+6) : Int)=2^(K+9) := by
        rw [show (8 : Int)=2^3 by norm_num,←pow_add]
        congr 1
        omega
      rw [he]

theorem actualCompiler : StandardSeededCompiler.ActualCompiler := by
  intro n d
  refine ⟨(SeededCompiler.Proof.compiler_bound d).1,(SeededCompiler.Proof.compiler_bound d).2,?_⟩
  intro policy ρ
  refine ⟨?_,compiler_difference policy d ρ⟩
  obtain ⟨av,ha,_,_⟩ := StandardFunctionalDetector.Proof.values_assignment policy ρ (SeededCompiler.compile d).pair.1
  obtain ⟨bv,hb,_,_⟩ := StandardFunctionalDetector.Proof.values_assignment policy ρ (SeededCompiler.compile d).pair.2
  refine ⟨av,bv,ha,hb,?_,?_⟩
  · rw [←StandardCombinatorCoordinates.Proof.value1_of_assignment Phi policy ρ _ _ ha]
    exact (StandardFunctionalDetector.Proof.values_facts policy ρ _).2.1
  · rw [←StandardCombinatorCoordinates.Proof.value1_of_assignment Phi policy ρ _ _ hb]
    exact (StandardFunctionalDetector.Proof.values_facts policy ρ _).2.1
end LogicLineages.PermittedControl.StandardSeededCompiler.Proof
