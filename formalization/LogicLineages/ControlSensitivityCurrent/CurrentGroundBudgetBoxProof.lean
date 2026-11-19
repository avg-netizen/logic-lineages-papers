module
public import LogicLineages.ControlSensitivityCurrent.CurrentGroundBudgetFloorProof
public import LogicLineages.ControlSensitivityCurrent.PolicyGadgetProof
public import LogicLineages.StandardControlCurrent.PolicyAssignmentStatementChecks
public import LogicLineages.OrdinalComparison.OriginalBudgetCodePrimitiveProof
public import LogicLineages.OrdinalComparison.OriginalBudgetCodeCountProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentGroundBudget

open LogicLineages.OrdinalComparison.Source
open LogicLineages.StandardControlCurrent
open AdmissibleSum AdmissibleAssignment HeadFiniteSurplus OriginalSecondBudget

theorem assignmentCode (p : Policy) {Γ τ} (t : OriginalTerm Γ τ) (u : OrdinalVector Γ τ.level)
    (hu : assignment p t = some u) :
    PolicyAssignment.assignmentCode p (Γ.map SyntaxCode.typeCode) (SyntaxCode.encodeTerm t) =
      some (OrdinalSyntax.vectorCode u) := by
  rw [PolicyAssignmentSyntaxProof.literal p Γ τ t,hu,Option.map_some]

theorem vectorZero {Γ m} (u : OrdinalVector Γ m) :
    (OrdinalSyntax.vectorCode u).getD 0 0 = OrdinalSyntax.typedCode (u 0) := by
  simp [OrdinalSyntax.vectorCode,List.getD_eq_getElem?_getD,List.getElem?_ofFn]

theorem functionalLevelOne (k : Nat) : (Ty.curriedGround (k+1)).level = 1 := by
  have hlo := (UnaryCarrier.headIndex k).isLt
  have hhi := AdditiveHeadTree.Proof.curried_level_bound (k+1)
  change 1 < (Ty.curriedGround (k+1)).level+1 at hlo
  omega

/-- Both positive coordinates of the original lambda agree literally, before
evaluation, with the successful actual body partial. -/
theorem abstractionPositive (p : Policy) (k : Nat) (Γ : List Ty)
    (u : OrdinalVector (Ty.curriedGround (k+1) :: Γ) 0)
    (v : OrdinalPartialVector Γ (Ty.curriedGround (k+1)))
    (B : OrdinalVector Γ (Ty.arrow (Ty.curriedGround (k+1)) Ty.ground).level)
    (hv : AdmissiblePartial.run p 0 (u 0) = some v) (hB : abstraction p u = some B) :
    B (boxFirst k) = v (outputOne k) ∧ B (boxSecond k) = v (outputTwo k) := by
  have hu : u = (fun _ : Fin 1 => u 0) := by funext j; rw [Fin.eq_zero j]
  rw [hu] at hB
  unfold abstraction at hB
  simp only [collect,Fin.val_zero,hv,Option.bind_some] at hB
  have sh : p.shape .positiveAbstraction 0 = .leaf := PolicyGadget.smallShapes.2.1 _
  constructor
  · have he := congrArg (fun w : OrdinalVector Γ (Ty.arrow (Ty.curriedGround (k+1)) Ty.ground).level =>
      w (boxFirst k)) (Option.some.inj hB)
    simpa [boxFirst,outputOne,functionalLevelOne,sh,expand,Fin.cases_zero,Ty.level] using he.symm
  · have he := congrArg (fun w : OrdinalVector Γ (Ty.arrow (Ty.curriedGround (k+1)) Ty.ground).level =>
      w (boxSecond k)) (Option.some.inj hB)
    simpa [boxSecond,outputTwo,functionalLevelOne,sh,expand,Fin.cases_zero,Ty.level] using he.symm

theorem fullBoxSecond (p : Policy) (k : Nat) (Γ : List Ty)
    (B : OrdinalVector Γ (Ty.arrow (Ty.curriedGround (k+1)) Ty.ground).level)
    (caller : OrdinalVector Γ (Ty.curriedGround (k+1)).level) :
    box p B caller (boxSecond k) = B (boxSecond k) := by
  change ordinalBoxPositive (Ty.curriedGround (k+1)).level (ordinalVectorAt B) (ordinalVectorAt caller) 2 = _
  rw [ordinalBoxPositive]
  split
  · have := functionalLevelOne k
    omega
  · unfold ordinalVectorAt
    rw [dif_pos (boxSecond k).isLt]
    rfl

theorem originalBox : CurrentGroundBudgetTargets.OriginalBox := by
  intro p k Γ P C ha
  obtain ⟨u,v,hu,hv,hbound,hval⟩ := sourceSecondFloor p k Γ 0 P
  obtain ⟨B,hB,_⟩ := actualAdmissibleAssignmentGenerated Γ
    (Ty.arrow (Ty.curriedGround (k+1)) Ty.ground) p (.lam (TrackedSource.erase P))
  obtain ⟨caller,hC,_⟩ := actualAdmissibleAssignmentGenerated Γ (Ty.curriedGround (k+1)) p C
  have hb : 4 ≤ scalarSecond (u 0) := by
    have h := (groundSourceFloor P ha).trans hbound
    exact_mod_cast h
  have hab := hB
  change (assignment p (TrackedSource.erase P)).bind (fun w => abstraction p w) = some B at hab
  rw [hu] at hab
  have hp := abstractionPositive p k Γ u v B hv hab
  refine ⟨u,B,caller,v,scalarSecond (u 0),hu,hB,hC,hv,hp.1,hp.2,rfl,hb,
    fullBoxSecond p k Γ B caller,?_,?_⟩
  · intro f ν
    rw [hp.2]
    exact hval f ν
  · rw [budgetCode,assignmentCode p _ u hu,Option.map_some,vectorZero]
    unfold OriginalBudgetCode.secondCode
    rw [OriginalBudgetCode.Proof.exactCounts Γ (Ty.curriedGround (k+1)) (u 0)]

theorem budgetEffective : CurrentGroundBudgetTargets.BudgetEffective := by
  intro p hp
  have ha := PolicyAssignmentRunPrograms.assignment p hp
  have hc := OriginalBudgetCode.Proof.primitiveRecursiveAlgorithms.2.1
  have h0 : Primrec (fun v : List Nat => OriginalBudgetCode.secondCode (v.getD 0 0)) :=
    hc.comp ((Primrec.list_getD 0).comp Primrec.id (Primrec.const 0))
  exact Computable.option_map ha (h0.to_comp.comp Computable.snd).to₂

end LogicLineages.ControlSensitivityCurrent.CurrentGroundBudget
