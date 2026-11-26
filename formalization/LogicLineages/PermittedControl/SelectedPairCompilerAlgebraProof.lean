module
public import LogicLineages.PermittedControl.SelectedPairCompilerTargets
public import LogicLineages.PermittedControl.SelectedHardnessProof
public import LogicLineages.OrdinalComparison.SourceSignedPairStructureProof
@[expose] public section
namespace LogicLineages.PermittedControl.SelectedPairCompiler.Proof
open OrdinalComparison Source Source.AdmissibleSum SelectedSourceDomain SignedPair
open SignedPair.Proof

theorem identity_head {Γ} (ctrl : Nat → Nat) (pol : Policy)
    (ρ : AdmissibleSubstitution ctrl Γ) : SelectedHardness.value1 ctrl pol ρ identity = 1 := by
  rw [SelectedHardnessCoordinatesProof.value1_of_assignment ctrl pol ρ _ _
    (SelectedHardnessPairSyntaxProof.identity_assignment pol Γ)]
  rfl

theorem variable_head {n} (ctrl : Nat → Nat) (pol : Policy)
    (ρ : AdmissibleSubstitution ctrl (Context n)) (i : Fin n) :
    SelectedHardness.value1 ctrl pol ρ (.var (inputVariable i)) = inputs ctrl ρ i := by
  rw [SelectedHardnessCoordinatesProof.value1_of_assignment ctrl pol ρ _ _ rfl]
  rfl

theorem join_difference (ctrl : Nat → Nat) (B : Nat) (hc : SelectedWithThreshold ctrl B) (pol : Policy) {Γ} (ρ : AdmissibleSubstitution ctrl Γ) (p q : Pair Γ) :
    difference ctrl pol ρ (join p q)=(8:Int) • (difference ctrl pol ρ p+difference ctrl pol ρ q) := by
  simp only [join,difference,(SelectedHardnessSignedProof.cnf_combine_selected ctrl B hc pol)]
  ext e
  simp only [Finsupp.add_apply,Finsupp.sub_apply,Finsupp.smul_apply,smul_eq_mul]
  ring

theorem eight_difference (ctrl : Nat → Nat) (B : Nat) (hc : SelectedWithThreshold ctrl B) (pol : Policy) {Γ} (ρ : AdmissibleSubstitution ctrl Γ) (p : Pair Γ) :
    difference ctrl pol ρ (timesEight p)=(8:Int) • difference ctrl pol ρ p := by
  simp only [timesEight,difference,(SelectedHardnessSignedProof.cnf_combine_selected ctrl B hc pol)]
  ext e
  simp only [Finsupp.add_apply,Finsupp.sub_apply,Finsupp.smul_apply,smul_eq_mul]
  ring

theorem sixteen_difference (ctrl : Nat → Nat) (B : Nat) (hc : SelectedWithThreshold ctrl B) (pol : Policy) {Γ} (ρ : AdmissibleSubstitution ctrl Γ) (p : Pair Γ) :
    difference ctrl pol ρ (timesSixteen p)=(16:Int) • difference ctrl pol ρ p := by
  rw [timesSixteen,(join_difference ctrl B hc pol)]
  ext e
  simp only [Finsupp.add_apply,Finsupp.smul_apply,smul_eq_mul]
  ring

theorem omega_difference (ctrl : Nat → Nat) (B : Nat) (hc : SelectedWithThreshold ctrl B) (pol : Policy) {Γ} (ρ : AdmissibleSubstitution ctrl Γ) (p : Pair Γ) :
    difference ctrl pol ρ (liftOmega p.1,liftOmega p.2)=(2:Int) • omegaShift (difference ctrl pol ρ p) := by
  simp only [difference,(SelectedHardnessSignedProof.cnf_omega_selected ctrl B hc pol),shift_sub]
  ext e
  simp only [Finsupp.add_apply,Finsupp.sub_apply,Finsupp.smul_apply,smul_eq_mul]
  ring

theorem iterate_difference (ctrl : Nat → Nat) (B : Nat) (hc : SelectedWithThreshold ctrl B) (pol : Policy) {Γ} (ρ : AdmissibleSubstitution ctrl Γ) (f : Pair Γ → Pair Γ) (c : Int)
    (hf : ∀p, difference ctrl pol ρ (f p)=c • difference ctrl pol ρ p) (k : Nat) (p : Pair Γ) :
    difference ctrl pol ρ ((f^[k]) p)=c^k • difference ctrl pol ρ p := by
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply',hf,ih,smul_smul,pow_succ']

theorem unit_difference (ctrl : Nat → Nat) (B : Nat) (hc : SelectedWithThreshold ctrl B) (pol : Policy) {Γ} (ρ : AdmissibleSubstitution ctrl Γ) :
    difference ctrl pol ρ unitPair=(2^12:Int) • signedCNF 1 := by
  simp only [unitPair,balanced,(join_difference ctrl B hc pol)]
  norm_num only [constantLeaf]
  simp only [if_true,if_false]
  simp only [difference,(SelectedHardnessSignedProof.cnf_combine_selected ctrl B hc pol),(SelectedHardnessSignedProof.cnf_project_selected ctrl B hc pol),(identity_head ctrl pol)]
  ext e
  simp only [Finsupp.add_apply,Finsupp.sub_apply,Finsupp.smul_apply,smul_eq_mul]
  ring

theorem variable_difference (ctrl : Nat → Nat) (B : Nat) (hc : SelectedWithThreshold ctrl B) (pol : Policy) {n} (ρ : AdmissibleSubstitution ctrl (Context n)) (i : Fin n) :
    difference ctrl pol ρ (variablePair i)=(2^15:Int) • signedCNF (inputs ctrl ρ i) := by
  rw [variablePair,(join_difference ctrl B hc pol),(iterate_difference ctrl B hc pol) ρ timesEight 8 ((eight_difference ctrl B hc pol) ρ),(unit_difference ctrl B hc pol)]
  simp only [difference,(SelectedHardnessSignedProof.cnf_project_selected ctrl B hc pol),(identity_head ctrl pol),(variable_head ctrl pol)]
  ext e
  simp only [Finsupp.add_apply,Finsupp.sub_apply,Finsupp.smul_apply,smul_eq_mul]
  ring

theorem padding_arithmetic (d : Nat) : (16:Int)^(d%3) * 8^(d/3+(2-d%3))=2^(d+6) := by
  rw [show (16:Int)=2^4 by norm_num,show (8:Int)=2^3 by norm_num,← pow_mul,← pow_mul,← pow_add]
  congr 1
  have hr := Nat.mod_lt d (by decide : 0<3)
  have hd := Nat.mod_add_div d 3
  omega

theorem pad_difference (ctrl : Nat → Nat) (B : Nat) (hc : SelectedWithThreshold ctrl B) (pol : Policy) {Γ} (ρ : AdmissibleSubstitution ctrl Γ) (d : Nat) (p : Pair Γ) :
    difference ctrl pol ρ (pad d p)=(2^(d+6):Int) • difference ctrl pol ρ p := by
  rw [pad,(iterate_difference ctrl B hc pol) ρ timesSixteen 16 ((sixteen_difference ctrl B hc pol) ρ),
    (iterate_difference ctrl B hc pol) ρ timesEight 8 ((eight_difference ctrl B hc pol) ρ),smul_smul,padding_arithmetic]

theorem pad_align (ctrl : Nat → Nat) (B : Nat) (hc : SelectedWithThreshold ctrl B) (pol : Policy) {Γ} (ρ : AdmissibleSubstitution ctrl Γ) (p : Pair Γ) (k K : Nat) (hk : k≤K)
    (d : CantorGroup) (hp : difference ctrl pol ρ p=(2^k:Int) • d) :
    difference ctrl pol ρ (pad (K-k) p)=(2^(K+6):Int) • d := by
  rw [(pad_difference ctrl B hc pol),hp,smul_smul,← pow_add]
  congr 2
  omega

theorem compiler_difference (ctrl : Nat → Nat) (B : Nat) (hc : SelectedWithThreshold ctrl B) (pol : Policy) {n} (d : Expression n) (ρ : AdmissibleSubstitution ctrl (Context n)) :
    difference ctrl pol ρ (compile d).pair=(2^(compile d).exponent:Int) • meaning (inputs ctrl ρ) d := by
  induction d with
  | unit => exact (unit_difference ctrl B hc pol) ρ
  | var i => exact (variable_difference ctrl B hc pol) ρ i
  | neg a ih =>
    change signedCNF (SelectedHardness.value1 ctrl pol ρ (compile a).pair.2)-signedCNF (SelectedHardness.value1 ctrl pol ρ (compile a).pair.1)=_
    rw [← neg_sub]
    change -difference ctrl pol ρ (compile a).pair=_
    rw [ih]
    change -((2^(compile a).exponent:Int) • meaning (inputs ctrl ρ) a)=
      (2^(compile a).exponent:Int) • (-meaning (inputs ctrl ρ) a)
    rw [smul_neg]
  | shift a ih =>
    change difference ctrl pol ρ (liftOmega (compile a).pair.1,liftOmega (compile a).pair.2)=_
    rw [(omega_difference ctrl B hc pol),ih,shift_smul,smul_smul]
    change (2*2^(compile a).exponent:Int) • omegaShift (meaning (inputs ctrl ρ) a)=
      (2^((compile a).exponent+1):Int) • omegaShift (meaning (inputs ctrl ρ) a)
    rw [pow_succ']
  | add a b iha ihb =>
    let K := max (compile a).exponent (compile b).exponent
    change difference ctrl pol ρ (join (pad (K-(compile a).exponent) (compile a).pair)
      (pad (K-(compile b).exponent) (compile b).pair))=(2^(K+9):Int) •
        (meaning (inputs ctrl ρ) a+meaning (inputs ctrl ρ) b)
    rw [(join_difference ctrl B hc pol),(pad_align ctrl B hc pol) ρ _ _ K (Nat.le_max_left _ _) _ iha,
      (pad_align ctrl B hc pol) ρ _ _ K (Nat.le_max_right _ _) _ ihb,← smul_add,smul_smul]
    have he : (8*2^(K+6):Int)=2^(K+9) := by
      rw [show (8:Int)=2^3 by norm_num,← pow_add]
      congr 1
      omega
    rw [he]

end LogicLineages.PermittedControl.SelectedPairCompiler.Proof
