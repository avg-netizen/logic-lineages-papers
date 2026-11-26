module
public import LogicLineages.PermittedControl.UniformPolicyCompilerTargets
public import LogicLineages.PermittedControl.UniformPolicyCompilerStepProof
import LogicLineages.OrdinalComparison.WWOrdinalSyntaxVectorCompilerComputability

@[expose] public section
namespace LogicLineages.PermittedControl.UniformPolicyCompiler
open OrdinalComparison Source Source.AdmissibleSum Source.SyntaxCode Source.OrdinalSyntax Source.ForwardTranslation
open PolicySuppliedCodeMacro (RealizesPolicy)
open StandardControlCurrent

/-- The uniform literal assignment, a fixed point of the step. -/
noncomputable def assignU : AArgs →. Option (List Nat) :=
  Classical.choose (exists_fix assignStep assignStepPartrec)

theorem assignUPartrec : Partrec assignU := (Classical.choose_spec (exists_fix assignStep assignStepPartrec)).1

theorem assignUFix (x : AArgs) : assignU x = assignStep assignU x :=
  (Classical.choose_spec (exists_fix assignStep assignStepPartrec)).2 x

theorem assignUCal {e : Code} {p : Policy} (he : RealizesPolicy e p) (Γ : List Nat) (n : Nat) :
    assignU (e,Γ,n) = Part.some (PolicyAssignment.assignmentCode p Γ n) := by
  induction n using Nat.strong_induction_on generalizing Γ with
  | _ n ih =>
    rw [assignUFix,PolicyAssignment.assignmentCode]
    unfold assignStep contBranch appBranch appMid appInner lamBranch lamInner
    apply pbind_calibrated
    intro resultType
    by_cases hlt : n % 8 < 5
    · rw [if_pos hlt,if_pos hlt]
      exact primeCal he _ _ _
    · rw [if_neg hlt,if_neg hlt]
      have hpos : 0 < n := by omega
      have hd : n/8 < n := Nat.div_lt_self hpos (by decide)
      have hl : (n/8).unpair.1 < n := (Nat.unpair_left_le _).trans_lt hd
      have hr : (n/8).unpair.2 < n := (Nat.unpair_right_le _).trans_lt hd
      by_cases h5 : n % 8 = 5
      · have hb : n % 8 = 5 ∨ n % 8 = 6 := Or.inl h5
        rw [if_pos h5,dif_pos hb,if_pos h5]
        apply pbind_calibrated
        intro argType
        rw [ih _ hl]
        apply pbind_calibrated
        intro f
        rw [ih _ hr]
        exact pbind_calibrated _ _ _ (fun a => applicationCal he _ _ _ _)
      · rw [if_neg h5]
        by_cases h6 : n % 8 = 6
        · have hb : n % 8 = 5 ∨ n % 8 = 6 := Or.inr h6
          rw [if_pos h6,dif_pos hb,if_neg h5]
          apply pbind_calibrated
          intro bodyType
          rw [ih _ hr]
          exact pbind_calibrated _ _ _ (fun b => abstractionCal he _ _ _)
        · have hb : ¬ (n % 8 = 5 ∨ n % 8 = 6) := by omega
          rw [if_neg h6,dif_neg hb]

/-! ## The uniform source compiler -/

noncomputable def compilePolicy (x : Code × Nat × Nat) : Part (Option EncodedVector) :=
  pbind (assignU (x.1,List.replicate x.2.1 0,x.2.2)) (fun v => Part.some (compileVectorCode v))

theorem compilePolicyPartrec : Partrec compilePolicy := by
  let A := Code × Nat × Nat
  have hctx : Computable (fun x : A => List.replicate x.2.1 0) :=
    replicateC.comp ((Computable.fst.comp Computable.snd).pair (Computable.const 0))
  have ha : Partrec (fun x : A => assignU (x.1,List.replicate x.2.1 0,x.2.2)) :=
    assignUPartrec.comp (Computable.fst.pair (hctx.pair (Computable.snd.comp Computable.snd)))
  have hv : Partrec₂ (fun (_ : A) (v : List Nat) => (Part.some (compileVectorCode v) : Part (Option EncodedVector))) :=
    (ordinalSyntaxVectorCompilerPrimitiveRecursive.to_comp.comp Computable.snd).partrec.to₂
  have h := pbindPartrec ha hv
  exact h

theorem compilePolicyCalibrated : Calibrated compilePolicy := by
  intro e p he d c
  change pbind (assignU (e,List.replicate d 0,c)) (fun v => Part.some (compileVectorCode v)) =
    Part.some (PolicySourceInterface.compile p d c)
  rw [assignUCal he]
  exact pbind_calibrated _ _ _ (fun v => rfl)

/-- The uniform source compiler: one partial recursive function of the supplied
policy program, calibrated to `PolicySourceInterface.compile`. -/
theorem exactUniformCompiler : ExactUniformCompiler :=
  ⟨compilePolicy,compilePolicyPartrec,compilePolicyCalibrated⟩

#print axioms compilePolicyPartrec
#print axioms compilePolicyCalibrated
#print axioms exactUniformCompiler
end LogicLineages.PermittedControl.UniformPolicyCompiler
