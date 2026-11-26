module
public import LogicLineages.PermittedControl.SelectedHardnessUnusedProof
public import LogicLineages.OrdinalComparison.SourceFunctionalDetectorCombinatorProof

@[expose] public section
namespace LogicLineages.PermittedControl.SelectedHardnessCombinatorSyntaxProof
open OrdinalComparison Source Source.AdmissibleAssignment Source.FunctionalDetector
open SelectedHardnessUnusedProof
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open SourceCollisionCompletion.Proof (weaken_free weaken_closure)

theorem app_assignment (p : AdmissibleSum.Policy) {Γ σ τ}
    (a : OriginalTerm Γ (.arrow σ τ)) (b : OriginalTerm Γ σ)
    (av : OrdinalVector Γ (Ty.arrow σ τ).level) (bv : OrdinalVector Γ σ.level)
    (ha : assignment p a = some av) (hb : assignment p b = some bv) :
    assignment p (.app a b) = some (application p av bv) := by
  simp [assignment,ha,hb]

def unusedHead {Γ} (a : OrdinalExpression Γ) : OrdinalExpression Γ :=
  .add (.add .one (.add a .one)) a

def higherUnusedVector (p : AdmissibleSum.Policy) {Γ} (v : OrdinalVector Γ 1) : OrdinalVector Γ 2 :=
  ![.add (repeated p .scalarRepeat 8 (.add (v 0) .one)) (v 0),
    unusedHead (v 1),.add .one .one]

def higherFreePart {Γ} (v : OrdinalVector Γ 1) (i : Fin 2) :
    OrdinalPartialVector Γ (.arrow .ground unary) :=
  fun j => if i.val=j.val then .add (v i) .one else .one

theorem higher_unused_assignment (p : AdmissibleSum.Policy) {Γ} (a : OriginalTerm Γ unary) (v : OrdinalVector Γ 1)
    (ha : assignment p a=some v) :
    assignment p
      (.lam (a.rename (Renaming.weaken Γ (.arrow .ground unary)))) = some (higherUnusedVector p v) := by
  have hp (i : Fin 2) : AdmissiblePartial.run p i.val
      (ordinalExpressionRename (Renaming.weaken Γ (.arrow .ground unary)) (v i)) =
      some (higherFreePart v i) := by
    rw [AdmissiblePartial.run.eq_def,weaken_free]
    simp only [if_true]
    apply congrArg some
    funext j
    simp only [ordinalFreePartialVector,weaken_closure,higherFreePart]
  have hz (i : Fin 2) : ordinalPartialSize
      (ordinalExpressionRename (Renaming.weaken Γ (.arrow .ground unary)) (v i))=1 := by
    rw [ordinalPartialSize.eq_def,weaken_free]
    rfl
  have hsize : ((List.ofFn (SourceRenaming.renameVector
      (Renaming.weaken Γ (.arrow .ground unary)) v)).map ordinalPartialSize).sum=2 := by
    simp [List.map_ofFn,Function.comp_def,SourceRenaming.renameVector,hz]
  simp only [assignment]
  rw [SourceRenaming.Proof.assignmentNaturality Γ ((.arrow .ground unary)::Γ) unary
    (Renaming.weaken Γ (.arrow .ground unary)) p a,ha]
  change abstraction p
    (SourceRenaming.renameVector (Renaming.weaken Γ (.arrow .ground unary)) v)=some (higherUnusedVector p v)
  unfold abstraction
  rw [hsize]
  have hps : (fun i : Fin 2 => AdmissiblePartial.run p i.val
      (SourceRenaming.renameVector (Renaming.weaken Γ (.arrow .ground unary)) v i))=
      (fun i => some (higherFreePart v i)) := funext hp
  rw [hps,AbsoluteObserver.Proof.collect_some]
  simp only [Option.bind_some]
  apply congrArg some
  funext j
  fin_cases j <;>
    simp [higherUnusedVector,unusedHead,higherFreePart,unary,Ty.level,
      SourceRenaming.renameVector,weaken_closure,shape1,AdmissibleSum.expand] <;> rfl

def combineVector (p : AdmissibleSum.Policy) {Γ} (av bv : OrdinalVector Γ 1) : OrdinalVector Γ 1 :=
  application (σ:=.arrow .ground unary) (τ:=unary) p
    (higherUnusedVector p av) (unusedVector p bv)

theorem combine_assignment (p : AdmissibleSum.Policy) {Γ} (a b : OriginalTerm Γ unary) (av bv : OrdinalVector Γ 1)
    (ha : assignment p a=some av)
    (hb : assignment p b=some bv) :
    assignment p (combine a b)=some (combineVector p av bv) :=
  app_assignment p _ _ _ _ (higher_unused_assignment p a av ha)
    (unused_assignment p b bv hb)

def combineHeadExpr {Γ} (av bv : OrdinalVector Γ 1) : OrdinalExpression Γ :=
  .emul (.add .one .one) (.add (unusedHead (av 1)) (unusedHead (bv 1)))

theorem combine_head_expression (p : AdmissibleSum.Policy) {Γ} (av bv : OrdinalVector Γ 1) :
    combineVector p av bv 1=combineHeadExpr av bv := by
  simp [combineVector,application,box,ordinalBoxPositive,ordinalVectorAt,higherUnusedVector,
    combineHeadExpr,unusedHead,unusedVector,freePart,
    unary,Ty.level,shape1,AdmissibleSum.expand]
  simp only [Nat.reduceMax, shape1, AdmissibleSum.expand]
  exact ⟨rfl,rfl,rfl,rfl⟩


end LogicLineages.PermittedControl.SelectedHardnessCombinatorSyntaxProof
