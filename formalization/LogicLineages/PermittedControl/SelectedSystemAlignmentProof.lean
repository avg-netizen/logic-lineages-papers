module
public import LogicLineages.PermittedControl.SelectedSystemRenamingProof
@[expose] public section
namespace LogicLineages.PermittedControl.SelectedSystemReduction.Proof
open OrdinalComparison Source SelectedSourceDomain SelectedFunctionalDetector
open Source.AdmissibleSum
open SelectedHardness (value1)
open SelectedFunctionalDetector.Proof
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

 theorem compiled_zero_iff (ctrl : Nat → Nat) (K : Nat) (hc : SelectedWithThreshold ctrl K)
    (policy : Policy) {n : Nat} (d : SignedPair.Expression n)
    (ρ : AdmissibleSubstitution ctrl (SignedPair.Context n)) :
    SignedPair.meaning (SelectedPairCompiler.inputs ctrl ρ) d=0 ↔
    value1 ctrl policy ρ (SignedPair.compile d).pair.1=value1 ctrl policy ρ (SignedPair.compile d).pair.2 := by
  have hcomp := SelectedPairCompiler.Proof.compiler_difference ctrl K hc policy d ρ
  have hs : (2^(SignedPair.compile d).exponent : Int)≠0 := pow_ne_zero _ (by decide)
  constructor
  · intro hd
    rw [hd,smul_zero] at hcomp
    apply signedCNF_injective
    exact sub_eq_zero.mp hcomp
  · intro hd
    have hz : SelectedPairCompiler.difference ctrl policy ρ (SignedPair.compile d).pair=0 := by
      unfold SelectedPairCompiler.difference
      rw [hd,sub_self]
    rw [hz] at hcomp
    ext e
    have he := congrArg (fun g : SignedPair.CantorGroup => g e) hcomp
    change 0=(2^(SignedPair.compile d).exponent : Int)*
      SignedPair.meaning (SelectedPairCompiler.inputs ctrl ρ) d e at he
    exact (mul_eq_zero.mp he.symm).resolve_left hs

 theorem headEqual_values {Γ} (ctrl : Nat → Nat) (K : Nat) (hc : SelectedWithThreshold ctrl K)
    (policy : Policy) (ρ : AdmissibleSubstitution ctrl Γ) (a b : OriginalTerm Γ unary) :
    HeadEqual ctrl policy ρ a b ↔ value1 ctrl policy ρ a=value1 ctrl policy ρ b := by
  obtain ⟨av,ha,h0,h1⟩ := values_assignment ctrl K hc policy ρ a
  obtain ⟨bv,hb,h0',h1'⟩ := values_assignment ctrl K hc policy ρ b
  rw [headEqual_iff ctrl policy ρ a b av bv ha hb,h1,h1']

 theorem pad_head_value {Γ} (ctrl : Nat → Nat) (K : Nat) (hc : SelectedWithThreshold ctrl K)
    (policy : Policy) (ρ : AdmissibleSubstitution ctrl Γ) (a : OriginalTerm Γ unary)
    (q : OriginalTerm Γ .ground) :
    value1 ctrl policy ρ (pad a q)=SelectedHardness.paddedHead (value1 ctrl policy ρ a) := by
  obtain ⟨av,ha,h0,h1⟩ := values_assignment ctrl K hc policy ρ a
  obtain ⟨qv,hq,hqs,hqp⟩ := ground_facts ctrl K hc policy q ρ
  rw [SelectedHardnessCoordinatesProof.value1_of_assignment ctrl policy ρ _ _
    (pad_assignment policy a q av qv ha hq)]
  change ParametricSourceSuccessor.denoteWith ctrl (valuation ctrl ρ) (padVector policy av qv 1)=_
  rw [pad_head]
  change SelectedHardness.paddedHead (expressionValue ctrl ρ (av 1))=_
  rw [h1]

 theorem aligned_reverse {Γ} (ctrl : Nat → Nat) (K : Nat) (hc : SelectedWithThreshold ctrl K)
    (policy : Policy) (a b : OriginalTerm Γ unary)
    (σ : AdmissibleSubstitution ctrl (.ground::.ground::Γ))
    (h : VectorEqual ctrl policy σ (alignedLeft a) (alignedRight b)) :
    value1 ctrl policy (pullback ctrl (shiftTwo Γ) σ) a=
      value1 ctrl policy (pullback ctrl (shiftTwo Γ) σ) b := by
  have he := (vector_equal_values ctrl K hc policy σ _ _).mp h
  have hh := he.2
  change value1 ctrl policy σ (pad (a.rename (shiftTwo Γ)) (.var .here))=
    value1 ctrl policy σ (pad (b.rename (shiftTwo Γ)) (.var (.there .here))) at hh
  rw [pad_head_value ctrl K hc policy,pad_head_value ctrl K hc policy] at hh
  have hv := FunctionalDetector.Proof.paddedHead_injective hh
  simpa only [head_preserves ctrl (shiftTwo Γ) (pullback ctrl (shiftTwo Γ) σ) σ
    (fun _ _ _ => rfl)] using hv
end LogicLineages.PermittedControl.SelectedSystemReduction.Proof
