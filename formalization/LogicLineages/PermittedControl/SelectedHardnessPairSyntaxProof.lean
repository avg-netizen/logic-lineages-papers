module
public import LogicLineages.PermittedControl.SelectedHardnessCombinatorSyntaxProof

@[expose] public section
namespace LogicLineages.PermittedControl.SelectedHardnessPairSyntaxProof
open OrdinalComparison Source Source.AdmissibleAssignment Source.FunctionalDetector Source.SignedPair
open SelectedHardnessUnusedProof SelectedHardnessCombinatorSyntaxProof
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open SourceCollisionCompletion.Proof (weaken_free weaken_closure)

def projectFreePart {Γ} (v : OrdinalVector Γ 1) (i : Fin 2) :
    OrdinalPartialVector Γ unary :=
  fun j => if i.val=j.val then .add (v i) .one else .one

theorem project_unused_assignment (p : AdmissibleSum.Policy) {Γ} (a : OriginalTerm Γ unary) (v : OrdinalVector Γ 1)
    (ha : assignment p a=some v) :
    assignment p
      (.lam (a.rename (Renaming.weaken Γ unary))) = some (higherUnusedVector p v) := by
  have hp (i : Fin 2) : AdmissiblePartial.run p i.val
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
    (Renaming.weaken Γ unary) p a,ha]
  change abstraction p
    (SourceRenaming.renameVector (Renaming.weaken Γ unary) v)=some (higherUnusedVector p v)
  unfold abstraction
  rw [hsize]
  have hps : (fun i : Fin 2 => AdmissiblePartial.run p i.val
      (SourceRenaming.renameVector (Renaming.weaken Γ unary) v i))=
      (fun i => some (projectFreePart v i)) := funext hp
  rw [hps,AbsoluteObserver.Proof.collect_some]
  simp only [Option.bind_some]
  apply congrArg some
  funext j
  fin_cases j <;>
    simp [higherUnusedVector,unusedHead,projectFreePart,unary,Ty.level,
      SourceRenaming.renameVector,weaken_closure,shape1,AdmissibleSum.expand] <;> rfl

def projectVector (p : AdmissibleSum.Policy) {Γ} (av bv : OrdinalVector Γ 1) : OrdinalVector Γ 1 :=
  application (σ:=unary) (τ:=unary) p (higherUnusedVector p av) bv

theorem project_assignment (p : AdmissibleSum.Policy) {Γ} (a b : OriginalTerm Γ unary) (av bv : OrdinalVector Γ 1)
    (ha : assignment p a=some av)
    (hb : assignment p b=some bv) :
    assignment p (project a b)=some (projectVector p av bv) :=
  app_assignment p _ _ _ _ (project_unused_assignment p a av ha) hb

theorem project_head_expression (p : AdmissibleSum.Policy) {Γ} (av bv : OrdinalVector Γ 1) :
    projectVector p av bv 1=.emul (.add .one .one) (.add (unusedHead (av 1)) (bv 1)) := by
  simp [projectVector,application,box,ordinalBoxPositive,ordinalVectorAt,higherUnusedVector,
    unusedHead,unary,Ty.level,shape1,AdmissibleSum.expand]
  exact ⟨rfl,rfl,rfl⟩

def omegaVector (p : AdmissibleSum.Policy) {Γ} (av : OrdinalVector Γ 1) : OrdinalVector Γ 1 :=
  application (σ:=.arrow .ground unary) (τ:=unary) p
    (application (σ:=.ground) (τ:=.arrow (.arrow .ground unary) unary) p
      (fun i => if i.val=0 then numeral p 2
        else if i.val=2 then .omega else .one) (fun _ => .one))
    (unusedVector p av)

theorem omega_assignment (p : AdmissibleSum.Policy) {Γ} (a : OriginalTerm Γ unary) (av : OrdinalVector Γ 1)
    (ha : assignment p a=some av) :
    assignment p (liftOmega a)=some (omegaVector p av) :=
  app_assignment p _ _ _ _
    (app_assignment p _ _ _ _ rfl rfl)
    (unused_assignment p a av ha)

theorem omega_head_expression (p : AdmissibleSum.Policy) {Γ} (av : OrdinalVector Γ 1) :
    omegaVector p av 1=.emul .omega (.add .one (unusedHead (av 1))) := by
  simp [omegaVector,application,box,ordinalBoxPositive,ordinalVectorAt,
    unusedVector,freePart,
    unusedHead,unary,Ty.level,shape1,AdmissibleSum.expand]
  refine ⟨?_,rfl⟩
  change AdmissibleSum.expand (p.shape .positiveAbstraction 1)
    (fun i : Fin 2 => if i.val = 1 then .add (av i) .one else .one) = _
  rw [shape1]
  rfl

def identityVector (Γ : List Ty) : OrdinalVector Γ 1 := ![.add (.add .one .one) .one,.one]

theorem identity_assignment (p : AdmissibleSum.Policy) (Γ : List Ty) :
    assignment p (@identity Γ)=some (identityVector Γ) := by
  apply congrArg some
  funext i
  fin_cases i <;>
    simp [identity,assignment,abstraction,collect,identityVector,Ty.level,
      AdmissiblePartial.run,ordinalPartialSize,ordinalHeadFree,ordinalHeadOccurs,
      ordinalHeadComponentOccurs,ordinalHeadClosure,ordinalHeadClosureComponent,
      substitute,AdmissibleAssignment.repeated,shape1,
      ControlSensitivityCurrent.PolicyGadget.smallShapes.2.1,AdmissibleSum.expand,
      ordinalFreePartialVector]
  all_goals first | rfl | exact ⟨rfl,rfl⟩


end LogicLineages.PermittedControl.SelectedHardnessPairSyntaxProof
