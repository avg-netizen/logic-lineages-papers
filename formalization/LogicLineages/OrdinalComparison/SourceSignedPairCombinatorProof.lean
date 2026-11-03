module
public import LogicLineages.OrdinalComparison.SourceSignedPairAlgebraProof
public import Mathlib.Tactic.Abel
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SignedPair.Proof
open OriginalDomain AdmissibleAssignment FunctionalDetector FunctionalDetector.Proof
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof
open SourceCollisionCompletion.Proof (weaken_free weaken_closure)

def projectFreePart {Γ} (v : OrdinalVector Γ 1) (i : Fin 2) :
    OrdinalPartialVector Γ unary :=
  fun j => if i.val=j.val then .add (v i) .one else .one

theorem project_unused_assignment {Γ} (a : OriginalTerm Γ unary) (v : OrdinalVector Γ 1)
    (ha : assignment OrdinalSyntax.defaultPolicy a=some v) :
    assignment OrdinalSyntax.defaultPolicy
      (.lam (a.rename (Renaming.weaken Γ unary))) = some (higherUnusedVector v) := by
  have hp (i : Fin 2) : AdmissiblePartial.run OrdinalSyntax.defaultPolicy i.val
      (ordinalExpressionRename (Renaming.weaken Γ unary) (v i)) =
      some (projectFreePart v i) := by
    rw [AdmissiblePartial.run.eq_def,weaken_free]
    simp only [if_true]
    apply congrArg some
    funext j
    simp only [ordinalFreePartialVector,weaken_closure,projectFreePart]
  have hz (i : Fin 2) : ordinalPartialSize
      (ordinalExpressionRename (Renaming.weaken Γ unary) (v i))=1 := by
    rw [ordinalPartialSize.eq_def,weaken_free]
    rfl
  have hsize : ((List.ofFn (SourceRenaming.renameVector
      (Renaming.weaken Γ unary) v)).map ordinalPartialSize).sum=2 := by
    simp [List.map_ofFn,Function.comp_def,SourceRenaming.renameVector,hz]
  simp only [assignment]
  rw [SourceRenaming.Proof.assignmentNaturality Γ (unary::Γ) unary
    (Renaming.weaken Γ unary) OrdinalSyntax.defaultPolicy a,ha]
  change abstraction OrdinalSyntax.defaultPolicy
    (SourceRenaming.renameVector (Renaming.weaken Γ unary) v)=some (higherUnusedVector v)
  unfold abstraction
  rw [hsize]
  have hps : (fun i : Fin 2 => AdmissiblePartial.run OrdinalSyntax.defaultPolicy i.val
      (SourceRenaming.renameVector (Renaming.weaken Γ unary) v i))=
      (fun i => some (projectFreePart v i)) := funext hp
  rw [hps,AbsoluteObserver.Proof.collect_some]
  simp only [Option.bind_some]
  apply congrArg some
  funext j
  fin_cases j <;>
    simp [higherUnusedVector,unusedHead,projectFreePart,unary,Ty.level,
      SourceRenaming.renameVector,weaken_closure,OrdinalSyntax.defaultPolicy,
      OrdinalSyntax.defaultShape,OrdinalSyntax.leftShape,AdmissibleSum.expand] <;> rfl

def projectVector {Γ} (av bv : OrdinalVector Γ 1) : OrdinalVector Γ 1 :=
  application (σ:=unary) (τ:=unary) OrdinalSyntax.defaultPolicy (higherUnusedVector av) bv

theorem project_assignment {Γ} (a b : OriginalTerm Γ unary) (av bv : OrdinalVector Γ 1)
    (ha : assignment OrdinalSyntax.defaultPolicy a=some av)
    (hb : assignment OrdinalSyntax.defaultPolicy b=some bv) :
    assignment OrdinalSyntax.defaultPolicy (project a b)=some (projectVector av bv) :=
  AbsoluteObserver.Proof.app_assignment _ _ _ _ (project_unused_assignment a av ha) hb

theorem project_head_expression {Γ} (av bv : OrdinalVector Γ 1) :
    projectVector av bv 1=.emul (.add .one .one) (.add (unusedHead (av 1)) (bv 1)) := by
  simp [projectVector,application,box,ordinalBoxPositive,ordinalVectorAt,higherUnusedVector,
    unusedHead,unary,Ty.level,OrdinalSyntax.defaultPolicy,OrdinalSyntax.defaultShape,
    OrdinalSyntax.leftShape,AdmissibleSum.expand]
  exact ⟨rfl,rfl,rfl⟩

theorem two_power_two : (2:Ordinal)^(ordinalNaturalSum 1 1)=4 := by
  have hs : ordinalNaturalSum (1:Ordinal) 1=2 := by
    simpa using naturalSum_finite 1 1
  rw [hs]
  exact_mod_cast (show (2:Nat)^2=4 by decide)

theorem project_head {Γ} (ρ : AdmissibleSubstitution Γ) (a b : OriginalTerm Γ unary) :
    value1 ρ (project a b)=ordinalNaturalProduct 4
      (ordinalNaturalSum (paddedHead (value1 ρ a)) (value1 ρ b)) := by
  obtain ⟨av,ha,ha0,ha1⟩ := values_assignment ρ a
  obtain ⟨bv,hb,hb0,hb1⟩ := values_assignment ρ b
  rw [value1_of_assignment ρ _ _ (project_assignment a b av bv ha hb),project_head_expression]
  change ordinalNaturalProduct ((2:Ordinal)^(ordinalNaturalSum 1 1))
    (ordinalNaturalSum (paddedHead (expressionValue ρ (av 1))) (expressionValue ρ (bv 1)))=_
  rw [two_power_two,ha1,hb1]

theorem cnf_padded (a : Ordinal) : signedCNF (paddedHead a)=
    (2:Int) • signedCNF a + (2:Int) • signedCNF 1 := by
  simp only [paddedHead,cnf_sum]
  ext e
  simp only [Finsupp.add_apply,Finsupp.smul_apply,smul_eq_mul]
  ring

theorem cnf_project {Γ} (ρ : AdmissibleSubstitution Γ) (a b : OriginalTerm Γ unary) :
    signedCNF (value1 ρ (project a b)) =
      (8:Int) • signedCNF (value1 ρ a) + (4:Int) • signedCNF (value1 ρ b) + (8:Int) • signedCNF 1 := by
  rw [project_head]
  have hb := sum_below_epsilon _ _ (paddedHead_below _ (values_facts ρ a).2.2.1)
    (values_facts ρ b).2.2.1
  have hc := cnf_finite_product (4:ℕ+) _ hb
  norm_num at hc
  rw [hc,cnf_sum,cnf_padded]
  ext e
  simp only [Finsupp.add_apply,Finsupp.smul_apply,smul_eq_mul]
  norm_num
  ring

theorem cnf_combine {Γ} (ρ : AdmissibleSubstitution Γ) (a b : OriginalTerm Γ unary) :
    signedCNF (value1 ρ (combine a b)) =
      (8:Int) • signedCNF (value1 ρ a) + (8:Int) • signedCNF (value1 ρ b) + (16:Int) • signedCNF 1 := by
  rw [combine_head,headCombine_four]
  have hb := sum_below_epsilon _ _ (paddedHead_below _ (values_facts ρ a).2.2.1)
    (paddedHead_below _ (values_facts ρ b).2.2.1)
  have hc := cnf_finite_product (4:ℕ+) _ hb
  norm_num at hc
  rw [hc,cnf_sum,cnf_padded,cnf_padded]
  ext e
  simp only [Finsupp.add_apply,Finsupp.smul_apply,smul_eq_mul]
  norm_num
  ring

def identityVector (Γ : List Ty) : OrdinalVector Γ 1 := ![.add (.add .one .one) .one,.one]

theorem identity_assignment (Γ : List Ty) :
    assignment OrdinalSyntax.defaultPolicy (@identity Γ)=some (identityVector Γ) := by
  apply congrArg some
  funext i
  fin_cases i <;>
    simp [identity,assignment,abstraction,collect,identityVector,Ty.level,
      AdmissiblePartial.run,ordinalPartialSize,ordinalHeadFree,ordinalHeadOccurs,
      ordinalHeadComponentOccurs,ordinalHeadClosure,ordinalHeadClosureComponent,
      substitute,AdmissibleAssignment.repeated,OrdinalSyntax.defaultPolicy,
      OrdinalSyntax.defaultShape,OrdinalSyntax.leftShape,AdmissibleSum.expand,
      ordinalFreePartialVector]
  all_goals first | rfl | exact ⟨rfl,rfl⟩

theorem identity_head {Γ} (ρ : AdmissibleSubstitution Γ) : value1 ρ identity=1 := by
  rw [value1_of_assignment ρ _ _ (identity_assignment Γ)]
  rfl

theorem variable_head {n} (ρ : AdmissibleSubstitution (Context n)) (i : Fin n) :
    value1 ρ (.var (inputVariable i))=inputs ρ i := by
  rw [value1_of_assignment ρ _ _ rfl]
  rfl

def omegaVector {Γ} (av : OrdinalVector Γ 1) : OrdinalVector Γ 1 :=
  application (σ:=.arrow .ground unary) (τ:=unary) OrdinalSyntax.defaultPolicy
    (application (σ:=.ground) (τ:=.arrow (.arrow .ground unary) unary) OrdinalSyntax.defaultPolicy
      (fun i => if i.val=0 then numeral OrdinalSyntax.defaultPolicy 2
        else if i.val=2 then .omega else .one) (fun _ => .one))
    (AbsoluteObserver.Proof.unusedVector av)

theorem omega_assignment {Γ} (a : OriginalTerm Γ unary) (av : OrdinalVector Γ 1)
    (ha : assignment OrdinalSyntax.defaultPolicy a=some av) :
    assignment OrdinalSyntax.defaultPolicy (liftOmega a)=some (omegaVector av) :=
  AbsoluteObserver.Proof.app_assignment _ _ _ _
    (AbsoluteObserver.Proof.app_assignment _ _ _ _ rfl rfl)
    (AbsoluteObserver.Proof.unused_assignment a av ha)

theorem omega_head_expression {Γ} (av : OrdinalVector Γ 1) :
    omegaVector av 1=.emul .omega (.add .one (unusedHead (av 1))) := by
  simp [omegaVector,application,box,ordinalBoxPositive,ordinalVectorAt,
    AbsoluteObserver.Proof.unusedVector,AbsoluteObserver.Proof.freePart,
    unusedHead,unary,Ty.level,OrdinalSyntax.defaultPolicy,OrdinalSyntax.defaultShape,
    OrdinalSyntax.leftShape,AdmissibleSum.expand]
  exact ⟨rfl,rfl⟩

theorem omega_head {Γ} (ρ : AdmissibleSubstitution Γ) (a : OriginalTerm Γ unary) :
    value1 ρ (liftOmega a)=ordinalNaturalProduct Ordinal.omega0
      (ordinalNaturalSum 1 (paddedHead (value1 ρ a))) := by
  obtain ⟨av,ha,ha0,ha1⟩ := values_assignment ρ a
  rw [value1_of_assignment ρ _ _ (omega_assignment a av ha),omega_head_expression]
  change ordinalNaturalProduct ((2:Ordinal)^Ordinal.omega0)
    (ordinalNaturalSum 1 (paddedHead (expressionValue ρ (av 1))))=_
  have hpow : (2:Ordinal)^Ordinal.omega0=Ordinal.omega0 := by
    simpa using Ordinal.natCast_opow_omega0 (by decide : 1<(2:Nat))
  rw [ha1,hpow]

theorem cnf_omega {Γ} (ρ : AdmissibleSubstitution Γ) (a : OriginalTerm Γ unary) :
    signedCNF (value1 ρ (liftOmega a))=
      (2:Int) • omegaShift (signedCNF (value1 ρ a)) + (3:Int) • omegaShift (signedCNF 1) := by
  rw [omega_head]
  have h1 : (1:Ordinal)<epsilonZero := by
    simpa only [ONote.repr_one,Nat.cast_one] using normalRepresentationSound (⟨1,ONote.nf_one⟩:NONote)
  rw [cnf_omega_product _ (sum_below_epsilon _ _ h1 (paddedHead_below _ (values_facts ρ a).2.2.1)),
    cnf_sum,cnf_padded,shift_add,shift_add,shift_smul,shift_smul]
  ext e
  simp only [Finsupp.add_apply,Finsupp.smul_apply,smul_eq_mul]
  ring
end LogicLineages.OrdinalComparison.Source.SignedPair.Proof
