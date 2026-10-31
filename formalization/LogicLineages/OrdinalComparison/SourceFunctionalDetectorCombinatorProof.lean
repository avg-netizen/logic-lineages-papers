module
public import LogicLineages.OrdinalComparison.SourceFunctionalDetectorTargets
public import LogicLineages.OrdinalComparison.SourceAbsoluteObserverProbeProof
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalDetector.Proof
open AdmissibleAssignment
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof
open SourceCollisionCompletion.Proof (weaken_free weaken_closure)

/-- The literal head obtained by unused abstraction of a unary source. -/
def unusedHead {Γ} (a : OrdinalExpression Γ) : OrdinalExpression Γ :=
  .add (.add .one (.add a .one)) a

def higherUnusedVector {Γ} (v : OrdinalVector Γ 1) : OrdinalVector Γ 2 :=
  ![.add (repeated OrdinalSyntax.defaultPolicy .scalarRepeat 8 (.add (v 0) .one)) (v 0),
    unusedHead (v 1),.add .one .one]

def higherFreePart {Γ} (v : OrdinalVector Γ 1) (i : Fin 2) :
    OrdinalPartialVector Γ (.arrow .ground unary) :=
  fun j => if i.val=j.val then .add (v i) .one else .one

theorem higher_unused_assignment {Γ} (a : OriginalTerm Γ unary) (v : OrdinalVector Γ 1)
    (ha : assignment OrdinalSyntax.defaultPolicy a=some v) :
    assignment OrdinalSyntax.defaultPolicy
      (.lam (a.rename (Renaming.weaken Γ (.arrow .ground unary)))) = some (higherUnusedVector v) := by
  have hp (i : Fin 2) : AdmissiblePartial.run OrdinalSyntax.defaultPolicy i.val
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
    (Renaming.weaken Γ (.arrow .ground unary)) OrdinalSyntax.defaultPolicy a,ha]
  change abstraction OrdinalSyntax.defaultPolicy
    (SourceRenaming.renameVector (Renaming.weaken Γ (.arrow .ground unary)) v)=some (higherUnusedVector v)
  unfold abstraction
  rw [hsize]
  have hps : (fun i : Fin 2 => AdmissiblePartial.run OrdinalSyntax.defaultPolicy i.val
      (SourceRenaming.renameVector (Renaming.weaken Γ (.arrow .ground unary)) v i))=
      (fun i => some (higherFreePart v i)) := funext hp
  rw [hps,AbsoluteObserver.Proof.collect_some]
  simp only [Option.bind_some]
  apply congrArg some
  funext j
  fin_cases j <;>
    simp [higherUnusedVector,unusedHead,higherFreePart,unary,Ty.level,
      SourceRenaming.renameVector,weaken_closure,OrdinalSyntax.defaultPolicy,
      OrdinalSyntax.defaultShape,OrdinalSyntax.leftShape,AdmissibleSum.expand] <;> rfl

def combineVector {Γ} (av bv : OrdinalVector Γ 1) : OrdinalVector Γ 1 :=
  application (σ:=.arrow .ground unary) (τ:=unary) OrdinalSyntax.defaultPolicy
    (higherUnusedVector av) (AbsoluteObserver.Proof.unusedVector bv)

theorem combine_assignment {Γ} (a b : OriginalTerm Γ unary) (av bv : OrdinalVector Γ 1)
    (ha : assignment OrdinalSyntax.defaultPolicy a=some av)
    (hb : assignment OrdinalSyntax.defaultPolicy b=some bv) :
    assignment OrdinalSyntax.defaultPolicy (combine a b)=some (combineVector av bv) :=
  AbsoluteObserver.Proof.app_assignment _ _ _ _ (higher_unused_assignment a av ha)
    (AbsoluteObserver.Proof.unused_assignment b bv hb)

def combineHeadExpr {Γ} (av bv : OrdinalVector Γ 1) : OrdinalExpression Γ :=
  .emul (.add .one .one) (.add (unusedHead (av 1)) (unusedHead (bv 1)))

theorem combine_head_expression {Γ} (av bv : OrdinalVector Γ 1) :
    combineVector av bv 1=combineHeadExpr av bv := by
  simp [combineVector,application,box,ordinalBoxPositive,ordinalVectorAt,higherUnusedVector,
    combineHeadExpr,unusedHead,AbsoluteObserver.Proof.unusedVector,AbsoluteObserver.Proof.freePart,
    unary,Ty.level,OrdinalSyntax.defaultPolicy,OrdinalSyntax.defaultShape,OrdinalSyntax.leftShape,AdmissibleSum.expand]
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem higher_unused_scalar {Γ} (ν : OrdinalComponent Γ → Ordinal) (av : OrdinalVector Γ 1)
    (a0 : Nat) (ha : denote ν (av 0)=(a0 : Ordinal)) :
    denote ν (higherUnusedVector av 0)=((9*a0+8 : Nat) : Ordinal) := by
  have ht : denote ν (.add (av 0) .one)=((a0+1 : Nat) : Ordinal) := by
    change ordinalNaturalSum (denote ν (av 0)) 1=_
    rw [ha]
    simpa only [Nat.cast_one] using naturalSum_finite a0 1
  change ordinalNaturalSum
    (denote ν (repeated OrdinalSyntax.defaultPolicy .scalarRepeat 8 (.add (av 0) .one)))
      (denote ν (av 0)) = _
  rw [AbsoluteObserver.Proof.repeated_value ν 8 (a0+1) _ ht,ha,naturalSum_finite]
  congr 1
  omega

theorem combine_scalar_value {Γ} (ν : OrdinalComponent Γ → Ordinal)
    (av bv : OrdinalVector Γ 1) (a0 b0 : Nat)
    (ha : denote ν (av 0)=(a0 : Ordinal)) (hb : denote ν (bv 0)=(b0 : Ordinal)) :
    denote ν (combineVector av bv 0) =
      (actualCollapse (ordinalNaturalSum
        (ordinalNaturalProduct Ordinal.omega0 (denote ν (combineHeadExpr av bv)))
        ((9*a0+5*b0+13 : Nat) : Ordinal)) : Ordinal) := by
  have hh : ordinalBoxPositive 1
      (@ordinalVectorAt Γ 2 (higherUnusedVector av))
      (@ordinalVectorAt Γ 1 (AbsoluteObserver.Proof.unusedVector bv)) 1=combineHeadExpr av bv := by
    exact combine_head_expression av bv
  have hb0 := AbsoluteObserver.Proof.unused_scalar (τ:=unary) ν bv b0 hb
  have hb0' : denote ν (AbsoluteObserver.Proof.unusedVector bv 0)=((5*b0+4 : Nat) : Ordinal) := by
    change denote ν (AbsoluteObserver.Proof.unusedVector bv 0)=((5*b0+(5-1) : Nat) : Ordinal) at hb0
    exact hb0
  have ht := AbsoluteObserver.Proof.box_tail_value ν 1 (9*a0+8) (5*b0+4)
    (higherUnusedVector av 0) (AbsoluteObserver.Proof.unusedVector bv 0)
      (higher_unused_scalar ν av a0 ha) hb0'
  have hn : 9*a0+8+(5*b0+4)+1=9*a0+5*b0+13 := by omega
  change denote ν (.collapse
    (ordinalBoxPositive 1 (@ordinalVectorAt Γ 2 (higherUnusedVector av))
      (@ordinalVectorAt Γ 1 (AbsoluteObserver.Proof.unusedVector bv)) 1)
    (boxTail OrdinalSyntax.defaultPolicy 1 (higherUnusedVector av 0)
      (AbsoluteObserver.Proof.unusedVector bv 0))) = _
  rw [hh]
  simp only [denote,ht,hn]

theorem unary_app_assignment {Γ} (a : OriginalTerm Γ unary) (q : OriginalTerm Γ .ground)
    (av : OrdinalVector Γ 1) (qv : OrdinalVector Γ 0)
    (ha : assignment OrdinalSyntax.defaultPolicy a=some av)
    (hq : assignment OrdinalSyntax.defaultPolicy q=some qv) :
    assignment OrdinalSyntax.defaultPolicy (.app a q)=
      some (application (σ:=.ground) (τ:=.ground) OrdinalSyntax.defaultPolicy av qv) :=
  AbsoluteObserver.Proof.app_assignment a q av qv ha hq

theorem unary_app_value {Γ} (ν : OrdinalComponent Γ → Ordinal)
    (av : OrdinalVector Γ 1) (qv : OrdinalVector Γ 0) (a0 q0 : Nat)
    (ha : denote ν (av 0)=(a0 : Ordinal)) (hq : denote ν (qv 0)=(q0 : Ordinal)) :
    denote ν (application (σ:=.ground) (τ:=.ground) OrdinalSyntax.defaultPolicy av qv 0)=
      (actualCollapse (ordinalNaturalSum (ordinalNaturalProduct Ordinal.omega0 (denote ν (av 1)))
        ((a0+q0 : Nat) : Ordinal)) : Ordinal) := by
  have he : application (σ:=.ground) (τ:=.ground) OrdinalSyntax.defaultPolicy av qv 0 =
      .collapse (av 1) (.add (av 0) (qv 0)) := by
    change Term.collapse (ordinalBoxPositive 0 (@ordinalVectorAt Γ 1 av) (@ordinalVectorAt Γ 0 qv) 1)
      (boxTail OrdinalSyntax.defaultPolicy 0 (av 0) (qv 0)) = _
    rw [ordinalBoxPositive]
    simp only [show ¬(1≤0) by omega,dite_false,boxTail,if_pos rfl,ordinalVectorAt]
    rfl
  rw [he]
  simp only [denote,ha,hq,naturalSum_finite]
end LogicLineages.OrdinalComparison.Source.FunctionalDetector.Proof
