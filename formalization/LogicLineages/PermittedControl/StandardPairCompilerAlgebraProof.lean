module
public import LogicLineages.PermittedControl.StandardPairCompilerTargets
public import LogicLineages.PermittedControl.StandardCombinatorCoordinatesProof
public import LogicLineages.OrdinalComparison.SourceSignedPairStructureProof
@[expose] public section
namespace LogicLineages.PermittedControl.StandardPairCompiler.Proof
open OrdinalComparison Source Source.AdmissibleSum SelectedSourceDomain SignedPair
open SignedPair.Proof

theorem identity_head {Γ} (ctrl : Nat → Nat) (pol : Policy)
    (ρ : AdmissibleSubstitution ctrl Γ) : SelectedHardness.value1 ctrl pol ρ identity = 1 := by
  rw [StandardCombinatorCoordinates.Proof.value1_of_assignment ctrl pol ρ _ _
    (SelectedHardnessPairSyntaxProof.identity_assignment pol Γ)]
  rfl

theorem variable_head {n} (ctrl : Nat → Nat) (pol : Policy)
    (ρ : AdmissibleSubstitution ctrl (Context n)) (i : Fin n) :
    SelectedHardness.value1 ctrl pol ρ (.var (inputVariable i)) = SelectedPairCompiler.inputs ctrl ρ i := by
  rw [StandardCombinatorCoordinates.Proof.value1_of_assignment ctrl pol ρ _ _ rfl]
  rfl

theorem join_difference  (pol : Policy) {Γ} (ρ : AdmissibleSubstitution Phi Γ) (p q : Pair Γ) :
    SelectedPairCompiler.difference Phi pol ρ (join p q)=(8:Int) • (SelectedPairCompiler.difference Phi pol ρ p+SelectedPairCompiler.difference Phi pol ρ q) := by
  simp only [join,SelectedPairCompiler.difference,(StandardCombinatorCoordinates.Proof.cnf_combine_selected  pol)]
  ext e
  simp only [Finsupp.add_apply,Finsupp.sub_apply,Finsupp.smul_apply,smul_eq_mul]
  ring

theorem eight_difference  (pol : Policy) {Γ} (ρ : AdmissibleSubstitution Phi Γ) (p : Pair Γ) :
    SelectedPairCompiler.difference Phi pol ρ (timesEight p)=(8:Int) • SelectedPairCompiler.difference Phi pol ρ p := by
  simp only [timesEight,SelectedPairCompiler.difference,(StandardCombinatorCoordinates.Proof.cnf_combine_selected  pol)]
  ext e
  simp only [Finsupp.add_apply,Finsupp.sub_apply,Finsupp.smul_apply,smul_eq_mul]
  ring

theorem sixteen_difference  (pol : Policy) {Γ} (ρ : AdmissibleSubstitution Phi Γ) (p : Pair Γ) :
    SelectedPairCompiler.difference Phi pol ρ (timesSixteen p)=(16:Int) • SelectedPairCompiler.difference Phi pol ρ p := by
  rw [timesSixteen,(join_difference  pol)]
  ext e
  simp only [Finsupp.add_apply,Finsupp.smul_apply,smul_eq_mul]
  ring

theorem omega_difference  (pol : Policy) {Γ} (ρ : AdmissibleSubstitution Phi Γ) (p : Pair Γ) :
    SelectedPairCompiler.difference Phi pol ρ (liftOmega p.1,liftOmega p.2)=(2:Int) • omegaShift (SelectedPairCompiler.difference Phi pol ρ p) := by
  simp only [SelectedPairCompiler.difference,(StandardCombinatorCoordinates.Proof.cnf_omega_selected  pol),shift_sub]
  ext e
  simp only [Finsupp.add_apply,Finsupp.sub_apply,Finsupp.smul_apply,smul_eq_mul]
  ring

theorem iterate_difference  (pol : Policy) {Γ} (ρ : AdmissibleSubstitution Phi Γ) (f : Pair Γ → Pair Γ) (c : Int)
    (hf : ∀p, SelectedPairCompiler.difference Phi pol ρ (f p)=c • SelectedPairCompiler.difference Phi pol ρ p) (k : Nat) (p : Pair Γ) :
    SelectedPairCompiler.difference Phi pol ρ ((f^[k]) p)=c^k • SelectedPairCompiler.difference Phi pol ρ p := by
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply',hf,ih,smul_smul,pow_succ']

theorem unit_difference  (pol : Policy) {Γ} (ρ : AdmissibleSubstitution Phi Γ) :
    SelectedPairCompiler.difference Phi pol ρ unitPair=(2^12:Int) • signedCNF 1 := by
  simp only [unitPair,balanced,(join_difference  pol)]
  norm_num only [constantLeaf]
  simp only [if_true,if_false]
  simp only [SelectedPairCompiler.difference,(StandardCombinatorCoordinates.Proof.cnf_combine_selected  pol),(StandardCombinatorCoordinates.Proof.cnf_project_selected  pol),(identity_head Phi pol)]
  ext e
  simp only [Finsupp.add_apply,Finsupp.sub_apply,Finsupp.smul_apply,smul_eq_mul]
  ring

theorem variable_difference  (pol : Policy) {n} (ρ : AdmissibleSubstitution Phi (Context n)) (i : Fin n) :
    SelectedPairCompiler.difference Phi pol ρ (variablePair i)=(2^15:Int) • signedCNF (SelectedPairCompiler.inputs Phi ρ i) := by
  rw [variablePair,(join_difference  pol),(iterate_difference  pol) ρ timesEight 8 ((eight_difference  pol) ρ),(unit_difference  pol)]
  simp only [SelectedPairCompiler.difference,(StandardCombinatorCoordinates.Proof.cnf_project_selected  pol),(identity_head Phi pol),(variable_head Phi pol)]
  ext e
  simp only [Finsupp.add_apply,Finsupp.sub_apply,Finsupp.smul_apply,smul_eq_mul]
  ring

theorem padding_arithmetic (d : Nat) : (16:Int)^(d%3) * 8^(d/3+(2-d%3))=2^(d+6) := by
  rw [show (16:Int)=2^4 by norm_num,show (8:Int)=2^3 by norm_num,← pow_mul,← pow_mul,← pow_add]
  congr 1
  have hr := Nat.mod_lt d (by decide : 0<3)
  have hd := Nat.mod_add_div d 3
  omega

theorem pad_difference  (pol : Policy) {Γ} (ρ : AdmissibleSubstitution Phi Γ) (d : Nat) (p : Pair Γ) :
    SelectedPairCompiler.difference Phi pol ρ (pad d p)=(2^(d+6):Int) • SelectedPairCompiler.difference Phi pol ρ p := by
  rw [pad,(iterate_difference  pol) ρ timesSixteen 16 ((sixteen_difference  pol) ρ),
    (iterate_difference  pol) ρ timesEight 8 ((eight_difference  pol) ρ),smul_smul,padding_arithmetic]

theorem pad_align  (pol : Policy) {Γ} (ρ : AdmissibleSubstitution Phi Γ) (p : Pair Γ) (k K : Nat) (hk : k≤K)
    (d : CantorGroup) (hp : SelectedPairCompiler.difference Phi pol ρ p=(2^k:Int) • d) :
    SelectedPairCompiler.difference Phi pol ρ (pad (K-k) p)=(2^(K+6):Int) • d := by
  rw [(pad_difference  pol),hp,smul_smul,← pow_add]
  congr 2
  omega

theorem compiler_difference  (pol : Policy) {n} (d : Expression n) (ρ : AdmissibleSubstitution Phi (Context n)) :
    SelectedPairCompiler.difference Phi pol ρ (compile d).pair=(2^(compile d).exponent:Int) • meaning (SelectedPairCompiler.inputs Phi ρ) d := by
  induction d with
  | unit => exact (unit_difference  pol) ρ
  | var i => exact (variable_difference  pol) ρ i
  | neg a ih =>
    change signedCNF (SelectedHardness.value1 Phi pol ρ (compile a).pair.2)-signedCNF (SelectedHardness.value1 Phi pol ρ (compile a).pair.1)=_
    rw [← neg_sub]
    change -SelectedPairCompiler.difference Phi pol ρ (compile a).pair=_
    rw [ih]
    change -((2^(compile a).exponent:Int) • meaning (SelectedPairCompiler.inputs Phi ρ) a)=
      (2^(compile a).exponent:Int) • (-meaning (SelectedPairCompiler.inputs Phi ρ) a)
    rw [smul_neg]
  | shift a ih =>
    change SelectedPairCompiler.difference Phi pol ρ (liftOmega (compile a).pair.1,liftOmega (compile a).pair.2)=_
    rw [(omega_difference  pol),ih,shift_smul,smul_smul]
    change (2*2^(compile a).exponent:Int) • omegaShift (meaning (SelectedPairCompiler.inputs Phi ρ) a)=
      (2^((compile a).exponent+1):Int) • omegaShift (meaning (SelectedPairCompiler.inputs Phi ρ) a)
    rw [pow_succ']
  | add a b iha ihb =>
    let K := max (compile a).exponent (compile b).exponent
    change SelectedPairCompiler.difference Phi pol ρ (join (pad (K-(compile a).exponent) (compile a).pair)
      (pad (K-(compile b).exponent) (compile b).pair))=(2^(K+9):Int) •
        (meaning (SelectedPairCompiler.inputs Phi ρ) a+meaning (SelectedPairCompiler.inputs Phi ρ) b)
    rw [(join_difference  pol),(pad_align  pol) ρ _ _ K (Nat.le_max_left _ _) _ iha,
      (pad_align  pol) ρ _ _ K (Nat.le_max_right _ _) _ ihb,← smul_add,smul_smul]
    have he : (8*2^(K+6):Int)=2^(K+9) := by
      rw [show (8:Int)=2^3 by norm_num,← pow_add]
      congr 1
      omega
    rw [he]

end LogicLineages.PermittedControl.StandardPairCompiler.Proof
