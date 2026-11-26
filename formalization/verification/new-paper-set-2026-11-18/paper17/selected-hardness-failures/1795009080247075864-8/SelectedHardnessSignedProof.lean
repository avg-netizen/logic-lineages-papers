module
public import LogicLineages.PermittedControl.SelectedHardnessValuesProof

@[expose] public section
namespace LogicLineages.PermittedControl.SelectedHardnessSignedProof
open OrdinalComparison Source Source.AdmissibleSum SelectedSourceDomain SelectedHardness
open Source.SignedPair Source.SignedPair.Proof
open SelectedHardnessCoordinatesProof SelectedHardnessValuesProof

private theorem one_below : (1 : Ordinal) < epsilonZero := by
  simpa only [ONote.repr_one,Nat.cast_one] using normalRepresentationSound (⟨1,ONote.nf_one⟩ : NONote)

private theorem head_below (ctrl : Nat → Nat) (K : Nat) (hc : SelectedWithThreshold ctrl K)
    {Γ} (p : Policy) (ρ : AdmissibleSubstitution ctrl Γ) (a : OriginalTerm Γ unary) :
    value1 ctrl p ρ a < epsilonZero := by
  obtain ⟨v,hv,h0,h1,hp0,hp1,he,hN⟩ := coordinateFacts ctrl K hc Γ p ρ a
  exact he

theorem cnf_project_selected (ctrl : Nat → Nat) (K : Nat) (hc : SelectedWithThreshold ctrl K)
    {Γ} (p : Policy) (ρ : AdmissibleSubstitution ctrl Γ) (a b : OriginalTerm Γ unary) :
    signedCNF (value1 ctrl p ρ (SelectedHardness.project a b)) =
      (8 : Int) • signedCNF (value1 ctrl p ρ a) + (4 : Int) • signedCNF (value1 ctrl p ρ b) +
      (8 : Int) • signedCNF 1 := by
  rw [project_head ctrl K hc]
  unfold projectHead
  change signedCNF (ordinalNaturalProduct 4 (ordinalNaturalSum (Source.FunctionalDetector.Proof.paddedHead (value1 ctrl p ρ a)) (value1 ctrl p ρ b))) = _
  have hb := Source.FunctionalDetector.Proof.sum_below_epsilon _ _
    (Source.FunctionalDetector.Proof.paddedHead_below _ (head_below ctrl K hc p ρ a)) (head_below ctrl K hc p ρ b)
  have hf := cnf_finite_product (4 : ℕ+) _ hb
  norm_num at hf
  rw [hf,cnf_sum,cnf_padded]
  ext e
  simp only [Finsupp.add_apply,Finsupp.smul_apply,smul_eq_mul]
  norm_num
  ring

theorem cnf_combine_selected (ctrl : Nat → Nat) (K : Nat) (hc : SelectedWithThreshold ctrl K)
    {Γ} (p : Policy) (ρ : AdmissibleSubstitution ctrl Γ) (a b : OriginalTerm Γ unary) :
    signedCNF (value1 ctrl p ρ (SelectedHardness.combine a b)) =
      (8 : Int) • signedCNF (value1 ctrl p ρ a) + (8 : Int) • signedCNF (value1 ctrl p ρ b) +
      (16 : Int) • signedCNF 1 := by
  rw [combine_head ctrl K hc]
  unfold combineHead
  change signedCNF (ordinalNaturalProduct 4 (ordinalNaturalSum (Source.FunctionalDetector.Proof.paddedHead (value1 ctrl p ρ a)) (Source.FunctionalDetector.Proof.paddedHead (value1 ctrl p ρ b)))) = _
  have hb := Source.FunctionalDetector.Proof.sum_below_epsilon _ _
    (Source.FunctionalDetector.Proof.paddedHead_below _ (head_below ctrl K hc p ρ a))
    (Source.FunctionalDetector.Proof.paddedHead_below _ (head_below ctrl K hc p ρ b))
  have hf := cnf_finite_product (4 : ℕ+) _ hb
  norm_num at hf
  rw [hf,cnf_sum,cnf_padded,cnf_padded]
  ext e
  simp only [Finsupp.add_apply,Finsupp.smul_apply,smul_eq_mul]
  norm_num
  ring

private theorem omega_one : ordinalNaturalProduct Ordinal.omega0 1 = Ordinal.omega0 := by
  let w : NONote := ⟨.oadd 1 1 .zero, ONote.NF.oadd ONote.nf_one 1 ONote.NFBelow.zero⟩
  let o : NONote := ⟨1, ONote.nf_one⟩
  have h := naturalProductDenotation w o
  have hw : w.1.repr = Ordinal.omega0 := by simp [w,ONote.repr]
  have ho : o.1.repr = 1 := by simp [o,ONote.repr_one]
  have hp : (naturalProduct w o).1 = w.1 := by
    change rawNaturalProduct (.oadd 1 1 .zero) (.oadd .zero 1 .zero) = .oadd 1 1 .zero
    have hz (x : ONote) : rawNaturalSum x .zero = x := by
      cases x <;> rw [rawNaturalSum]
    simp only [rawNaturalProduct,rawMonomialProduct,hz]
    congr 2
    exact one_mul (1 : ℕ+)
  rw [hp,hw,ho] at h
  exact h.symm

private theorem shift_one : omegaShift (signedCNF 1) = signedCNF Ordinal.omega0 := by
  have h := cnf_omega_product 1 one_below
  rw [omega_one] at h
  exact h.symm

theorem cnf_omega_selected (ctrl : Nat → Nat) (K : Nat) (hc : SelectedWithThreshold ctrl K)
    {Γ} (p : Policy) (ρ : AdmissibleSubstitution ctrl Γ) (a : OriginalTerm Γ unary) :
    signedCNF (value1 ctrl p ρ (SelectedHardness.liftOmega a)) =
      (2 : Int) • omegaShift (signedCNF (value1 ctrl p ρ a)) + (3 : Int) • signedCNF Ordinal.omega0 := by
  rw [omega_head ctrl K hc]
  change signedCNF (ordinalNaturalProduct Ordinal.omega0 (ordinalNaturalSum 1 (Source.FunctionalDetector.Proof.paddedHead (value1 ctrl p ρ a)))) = _
  have hb := Source.FunctionalDetector.Proof.sum_below_epsilon _ _ one_below
    (Source.FunctionalDetector.Proof.paddedHead_below _ (head_below ctrl K hc p ρ a))
  rw [cnf_omega_product _ hb,cnf_sum,cnf_padded,shift_add,shift_add,shift_smul,shift_smul,shift_one]
  ext e
  simp only [Finsupp.add_apply,Finsupp.smul_apply,smul_eq_mul]
  ring

private theorem signed_injective : Function.Injective signedCNF := by
  intro a b hab
  apply Ordinal.CNF.coeff_injective Ordinal.omega0
  ext e
  have h := congrArg (fun g : CantorGroup => g e) hab
  simp only [cnf_apply] at h
  obtain ⟨m,hm⟩ := Ordinal.lt_omega0.mp (Source.FunctionalDetector.Proof.coeff_finite a e)
  obtain ⟨n,hn⟩ := Ordinal.lt_omega0.mp (Source.FunctionalDetector.Proof.coeff_finite b e)
  rw [hm,hn,finite_nat,finite_nat] at h
  have he : m = n := by exact_mod_cast h
  rw [hm,hn,he]

theorem lift_head (ctrl : Nat → Nat) (K : Nat) (hc : SelectedWithThreshold ctrl K)
    {Γ} (p : Policy) (ρ : AdmissibleSubstitution ctrl Γ) (a : OriginalTerm Γ unary) :
    value1 ctrl p ρ (SelectedHardness.liftOmega a) = liftHead (value1 ctrl p ρ a) := by
  apply signed_injective
  rw [cnf_omega_selected ctrl K hc,liftHead,cnf_sum]
  have he := SelectedValueClosureProof.product_below SelectedValueClosureProof.omega_below (head_below ctrl K hc p ρ a)
  have h2 := cnf_finite_product (2 : ℕ+) _ he
  have h3 := cnf_finite_product (3 : ℕ+) Ordinal.omega0 SelectedValueClosureProof.omega_below
  norm_num at h2 h3
  rw [h2,h3,cnf_omega_product _ (head_below ctrl K hc p ρ a)]

theorem signedCombinatorValues : SelectedHardnessTargets.SignedCombinatorValues := by
  intro ctrl K hc Γ p ρ a b
  exact ⟨cnf_project_selected ctrl K hc p ρ a b,cnf_combine_selected ctrl K hc p ρ a b,
    cnf_omega_selected ctrl K hc p ρ a⟩

end LogicLineages.PermittedControl.SelectedHardnessSignedProof
