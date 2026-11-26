module
public import LogicLineages.PermittedControl.StandardSystemRenamingProof
@[expose] public section
namespace LogicLineages.PermittedControl.StandardSystemMask.Proof
open OrdinalComparison Source SelectedSourceDomain SelectedFunctionalDetector
open Source.AdmissibleSum
open SelectedHardness (value1)
open StandardFunctionalDetector.Proof
open SelectedSystemReduction
open StandardCombinatorCoordinates.Proof (padVector pad_assignment pad_head pad_scalar)
open Source.FunctionalDetector (unary shiftTwo pad alignedLeft alignedRight)

private theorem signedCNF_injective : Function.Injective SignedPair.signedCNF := by
  intro a b hab
  apply Ordinal.CNF.coeff_injective Ordinal.omega0
  ext e
  obtain ⟨m,hm⟩ := Ordinal.lt_omega0.mp (FunctionalDetector.Proof.coeff_finite a e)
  obtain ⟨n,hn⟩ := Ordinal.lt_omega0.mp (FunctionalDetector.Proof.coeff_finite b e)
  have he := congrArg (fun g : SignedPair.CantorGroup => g e) hab
  simp only [SignedPair.Proof.cnf_apply,hm,hn,SignedPair.Proof.finite_nat] at he
  have hmn : m=n := by exact_mod_cast he
  rw [hm,hn,hmn]

 theorem compiled_zero_iff 
    (policy : Policy) {n : Nat} (d : SignedPair.Expression n)
    (ρ : AdmissibleSubstitution Phi (SignedPair.Context n)) :
    SignedPair.meaning (SelectedPairCompiler.inputs Phi ρ) d=0 ↔
    value1 Phi policy ρ (SignedPair.compile d).pair.1=value1 Phi policy ρ (SignedPair.compile d).pair.2 := by
  have hcomp := StandardPairCompiler.Proof.compiler_difference  policy d ρ
  have hs : (2^(SignedPair.compile d).exponent : Int)≠0 := pow_ne_zero _ (by decide)
  constructor
  · intro hd
    rw [hd,smul_zero] at hcomp
    apply signedCNF_injective
    exact sub_eq_zero.mp hcomp
  · intro hd
    have hz : SelectedPairCompiler.difference Phi policy ρ (SignedPair.compile d).pair=0 := by
      unfold SelectedPairCompiler.difference
      rw [hd,sub_self]
    rw [hz] at hcomp
    ext e
    have he := congrArg (fun g : SignedPair.CantorGroup => g e) hcomp
    change 0=(2^(SignedPair.compile d).exponent : Int)*
      SignedPair.meaning (SelectedPairCompiler.inputs Phi ρ) d e at he
    exact (mul_eq_zero.mp he.symm).resolve_left hs

 theorem headEqual_values {Γ} 
    (policy : Policy) (ρ : AdmissibleSubstitution Phi Γ) (a b : OriginalTerm Γ unary) :
    HeadEqual Phi policy ρ a b ↔ value1 Phi policy ρ a=value1 Phi policy ρ b := by
  obtain ⟨av,ha,h0,h1⟩ := values_assignment  policy ρ a
  obtain ⟨bv,hb,h0',h1'⟩ := values_assignment  policy ρ b
  rw [headEqual_iff Phi policy ρ a b av bv ha hb,h1,h1']

 theorem pad_head_value {Γ} 
    (policy : Policy) (ρ : AdmissibleSubstitution Phi Γ) (a : OriginalTerm Γ unary)
    (q : OriginalTerm Γ .ground) :
    value1 Phi policy ρ (pad a q)=SelectedHardness.paddedHead (value1 Phi policy ρ a) := by
  obtain ⟨av,ha,h0,h1⟩ := values_assignment  policy ρ a
  obtain ⟨qv,hq,hqs,hqp⟩ := ground_facts  policy q ρ
  rw [StandardCombinatorCoordinates.Proof.value1_of_assignment Phi policy ρ _ _
    (pad_assignment policy a q av qv ha hq)]
  change ParametricSourceSuccessor.denoteWith Phi (valuation Phi ρ) (padVector policy av qv 1)=_
  rw [pad_head]
  change SelectedHardness.paddedHead (expressionValue Phi ρ (av 1))=_
  rw [h1]

 theorem aligned_reverse {Γ} 
    (policy : Policy) (a b : OriginalTerm Γ unary)
    (σ : AdmissibleSubstitution Phi (.ground::.ground::Γ))
    (h : VectorEqual Phi policy σ (alignedLeft a) (alignedRight b)) :
    value1 Phi policy (pullback Phi (shiftTwo Γ) σ) a=
      value1 Phi policy (pullback Phi (shiftTwo Γ) σ) b := by
  have he := (vector_equal_values  policy σ _ _).mp h
  have hh := he.2
  change value1 Phi policy σ (pad (a.rename (shiftTwo Γ)) (.var .here))=
    value1 Phi policy σ (pad (b.rename (shiftTwo Γ)) (.var (.there .here))) at hh
  rw [pad_head_value  policy,pad_head_value  policy] at hh
  have hv := FunctionalDetector.Proof.paddedHead_injective hh
  simpa only [head_preserves Phi (shiftTwo Γ) (pullback Phi (shiftTwo Γ) σ) σ
    (fun _ _ _ => rfl)] using hv
end LogicLineages.PermittedControl.StandardSystemMask.Proof
