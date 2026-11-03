module
public import LogicLineages.OrdinalComparison.SourceSignedPairCombinatorProof
public import LogicLineages.OrdinalComparison.SourceSignedPairStructureProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SignedPair.Proof
open OriginalDomain FunctionalDetector FunctionalDetector.Proof

theorem join_difference {Γ} (ρ : AdmissibleSubstitution Γ) (p q : Pair Γ) :
    difference ρ (join p q)=(8:Int) • (difference ρ p+difference ρ q) := by
  simp only [join,difference,cnf_combine]
  ext e
  simp only [Finsupp.add_apply,Finsupp.sub_apply,Finsupp.smul_apply,smul_eq_mul]
  ring

theorem eight_difference {Γ} (ρ : AdmissibleSubstitution Γ) (p : Pair Γ) :
    difference ρ (timesEight p)=(8:Int) • difference ρ p := by
  simp only [timesEight,difference,cnf_combine]
  ext e
  simp only [Finsupp.add_apply,Finsupp.sub_apply,Finsupp.smul_apply,smul_eq_mul]
  ring

theorem sixteen_difference {Γ} (ρ : AdmissibleSubstitution Γ) (p : Pair Γ) :
    difference ρ (timesSixteen p)=(16:Int) • difference ρ p := by
  rw [timesSixteen,join_difference]
  ext e
  simp only [Finsupp.add_apply,Finsupp.smul_apply,smul_eq_mul]
  ring

theorem omega_difference {Γ} (ρ : AdmissibleSubstitution Γ) (p : Pair Γ) :
    difference ρ (liftOmega p.1,liftOmega p.2)=(2:Int) • omegaShift (difference ρ p) := by
  simp only [difference,cnf_omega,shift_sub]
  ext e
  simp only [Finsupp.add_apply,Finsupp.sub_apply,Finsupp.smul_apply,smul_eq_mul]
  ring

theorem iterate_difference {Γ} (ρ : AdmissibleSubstitution Γ) (f : Pair Γ → Pair Γ) (c : Int)
    (hf : ∀p, difference ρ (f p)=c • difference ρ p) (k : Nat) (p : Pair Γ) :
    difference ρ ((f^[k]) p)=c^k • difference ρ p := by
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply',hf,ih,smul_smul,pow_succ']

theorem unit_difference {Γ} (ρ : AdmissibleSubstitution Γ) :
    difference ρ unitPair=(2^12:Int) • signedCNF 1 := by
  simp only [unitPair,balanced,join_difference]
  norm_num only [constantLeaf]
  simp only [if_true,if_false]
  simp only [difference,cnf_combine,cnf_project,identity_head]
  ext e
  simp only [Finsupp.add_apply,Finsupp.sub_apply,Finsupp.smul_apply,smul_eq_mul]
  ring

theorem variable_difference {n} (ρ : AdmissibleSubstitution (Context n)) (i : Fin n) :
    difference ρ (variablePair i)=(2^15:Int) • signedCNF (inputs ρ i) := by
  rw [variablePair,join_difference,iterate_difference ρ timesEight 8 (eight_difference ρ),unit_difference]
  simp only [difference,cnf_project,identity_head,variable_head]
  ext e
  simp only [Finsupp.add_apply,Finsupp.sub_apply,Finsupp.smul_apply,smul_eq_mul]
  ring

theorem padding_arithmetic (d : Nat) : (16:Int)^(d%3) * 8^(d/3+(2-d%3))=2^(d+6) := by
  rw [show (16:Int)=2^4 by norm_num,show (8:Int)=2^3 by norm_num,← pow_mul,← pow_mul,← pow_add]
  congr 1
  have hr := Nat.mod_lt d (by decide : 0<3)
  have hd := Nat.mod_add_div d 3
  omega

theorem pad_difference {Γ} (ρ : AdmissibleSubstitution Γ) (d : Nat) (p : Pair Γ) :
    difference ρ (pad d p)=(2^(d+6):Int) • difference ρ p := by
  rw [pad,iterate_difference ρ timesSixteen 16 (sixteen_difference ρ),
    iterate_difference ρ timesEight 8 (eight_difference ρ),smul_smul,padding_arithmetic]

theorem pad_align {Γ} (ρ : AdmissibleSubstitution Γ) (p : Pair Γ) (k K : Nat) (hk : k≤K)
    (d : CantorGroup) (hp : difference ρ p=(2^k:Int) • d) :
    difference ρ (pad (K-k) p)=(2^(K+6):Int) • d := by
  rw [pad_difference,hp,smul_smul,← pow_add]
  congr 2
  omega

theorem compiler_difference {n} (d : Expression n) (ρ : AdmissibleSubstitution (Context n)) :
    difference ρ (compile d).pair=(2^(compile d).exponent:Int) • meaning (inputs ρ) d := by
  induction d with
  | unit => exact unit_difference ρ
  | var i => exact variable_difference ρ i
  | neg a ih =>
    change signedCNF (value1 ρ (compile a).pair.2)-signedCNF (value1 ρ (compile a).pair.1)=_
    rw [← neg_sub]
    change -difference ρ (compile a).pair=_
    rw [ih]
    change -((2^(compile a).exponent:Int) • meaning (inputs ρ) a)=
      (2^(compile a).exponent:Int) • (-meaning (inputs ρ) a)
    rw [smul_neg]
  | shift a ih =>
    change difference ρ (liftOmega (compile a).pair.1,liftOmega (compile a).pair.2)=_
    rw [omega_difference,ih,shift_smul,smul_smul]
    change (2*2^(compile a).exponent:Int) • omegaShift (meaning (inputs ρ) a)=
      (2^((compile a).exponent+1):Int) • omegaShift (meaning (inputs ρ) a)
    rw [pow_succ']
  | add a b iha ihb =>
    let K := max (compile a).exponent (compile b).exponent
    change difference ρ (join (pad (K-(compile a).exponent) (compile a).pair)
      (pad (K-(compile b).exponent) (compile b).pair))=(2^(K+9):Int) •
        (meaning (inputs ρ) a+meaning (inputs ρ) b)
    rw [join_difference,pad_align ρ _ _ K (Nat.le_max_left _ _) _ iha,
      pad_align ρ _ _ K (Nat.le_max_right _ _) _ ihb,← smul_add,smul_smul]
    have he : (8*2^(K+6):Int)=2^(K+9) := by
      rw [show (8:Int)=2^3 by norm_num,← pow_add]
      congr 1
      omega
    rw [he]

theorem signedPairCompiler : Targets.SignedPairCompiler := by
  intro n d
  refine ⟨(compiler_bound d).1,(compiler_bound d).2,?_⟩
  intro ρ
  exact ⟨(values_facts ρ _).2.1,(values_facts ρ _).2.1,compiler_difference d ρ⟩
end LogicLineages.OrdinalComparison.Source.SignedPair.Proof
