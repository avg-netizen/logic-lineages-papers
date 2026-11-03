module
public import LogicLineages.OrdinalComparison.AdditiveHeadTreeTargets
public import LogicLineages.OrdinalComparison.ActiveScalarAnnotationStructureProof
public import LogicLineages.OrdinalComparison.WWGeneratedGradeProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.AdditiveHeadTree.Proof
open ActiveScalarAnnotation AssignmentSupport AssignmentSupport.Proof AdmissibleSum

theorem head_grade {k Γ} {F : Variable Γ (Ty.curriedGround (k+1))}
    {e : OrdinalExpression Γ} (h : HeadTree F e) : GeneratedOrdinalGrade Γ 1 e := by
  induction h with
  | free hg _ => exact hg
  | tracked => exact .var F (UnaryCarrier.headIndex k)
  | add _ _ iha ihb => exact .add iha ihb

theorem scalar_grade {k Γ} {F : Variable Γ (Ty.curriedGround (k+1))}
    {e : OrdinalExpression Γ} (h : ScalarTrees F e) : GeneratedOrdinalGrade Γ 0 e := by
  induction h with
  | free hg _ => exact hg
  | tracked => exact .var F 0
  | add _ _ iha ihb => exact .add iha ihb
  | collapse hh _ ih => exact .collapse (head_grade hh) ih

theorem head_one {k Γ} (F : Variable Γ (Ty.curriedGround (k+1))) : HeadTree F .one :=
  .free (.one 1) (by simp [Active])

theorem scalar_one {k Γ} (F : Variable Γ (Ty.curriedGround (k+1))) : ScalarTrees F .one :=
  .free (.one 0) (by simp [Active])

theorem head_expand {k Γ n} (F : Variable Γ (Ty.curriedGround (k+1)))
    (s : Shape n) (xs : Fin n → OrdinalExpression Γ) (h : ∀ i, HeadTree F (xs i)) :
    HeadTree F (expand s xs) := by
  induction s with
  | leaf => exact h 0
  | @join n m a b iha ihb =>
    exact .add (iha _ (fun i => h (Fin.castAdd m i)))
      (ihb _ (fun i => h (Fin.natAdd n i)))

theorem scalar_expand {k Γ n} (F : Variable Γ (Ty.curriedGround (k+1)))
    (s : Shape n) (xs : Fin n → OrdinalExpression Γ) (h : ∀ i, ScalarTrees F (xs i)) :
    ScalarTrees F (expand s xs) := by
  induction s with
  | leaf => exact h 0
  | @join n m a b iha ihb =>
    exact .add (iha _ (fun i => h (Fin.castAdd m i)))
      (ihb _ (fun i => h (Fin.natAdd n i)))

theorem scalar_repeated {k Γ} (p : Policy) (F : Variable Γ (Ty.curriedGround (k+1)))
    (site : MacroSite) (n : Nat) (q : OrdinalExpression Γ) (hn : 0 < n)
    (hq : ScalarTrees F q) : ScalarTrees F (AdmissibleAssignment.repeated p site n q) := by
  cases n with
  | zero => omega
  | succ n => exact scalar_expand F (p.shape site n) (fun _ => q) (fun _ => hq)

theorem headClosureHead : Targets.HeadClosureHead := by
  intro k Γ F h hh
  induction hh with
  | free hg hn =>
    exact .free (actualGeneratedGradeHeadClosure Γ .ground 1 _ hg)
      (fun ha => hn ((ActiveScalarAnnotation.Proof.active_headClosure F _).mp ha))
  | tracked => exact .tracked
  | add _ _ iha ihb => exact .add iha ihb

theorem headClosureScalar : Targets.HeadClosureScalar := by
  intro k Γ F q hq
  induction hq with
  | free hg hn =>
    exact .free (actualGeneratedGradeHeadClosure Γ .ground 0 _ hg)
      (fun ha => hn ((ActiveScalarAnnotation.Proof.active_headClosure F _).mp ha))
  | tracked => exact .tracked
  | add _ _ iha ihb => exact .add iha ihb
  | collapse hh _ ih => exact .collapse (headClosureHead k Γ F _ hh) ih

end LogicLineages.OrdinalComparison.Source.AdditiveHeadTree.Proof
