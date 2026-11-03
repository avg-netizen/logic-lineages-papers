module
public import LogicLineages.OrdinalComparison.ActiveScalarAnnotationTargets
public import LogicLineages.OrdinalComparison.SourceAssignmentSupportStructureProof
public import LogicLineages.OrdinalComparison.TrackedSourceProof
public import LogicLineages.OrdinalComparison.GroundOperatorDischargeProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ActiveScalarAnnotation.Proof
open SourceFreeOccurrences AssignmentSupport AssignmentSupport.Proof AdmissibleSum

@[simp] theorem active_headClosure {k Γ} (F : Variable Γ (Ty.curriedGround (k+1)))
    (q : OrdinalExpression (.ground :: Γ)) :
    Active F (ordinalHeadClosure q) ↔ Active (.there F) q := by
  unfold Active
  rw [names_headClosure, TrackedSource.Proof.mem_dropBound]

theorem annotated_expand {k Γ n} (p : Policy) (F : Variable Γ (Ty.curriedGround (k+1)))
    (s : Shape n) (xs : Fin n → OrdinalExpression Γ)
    (h : ∀ i, Annotated p F (xs i)) : Annotated p F (expand s xs) := by
  induction s with
  | leaf => exact h 0
  | @join n m a b iha ihb =>
    exact .add (iha _ (fun i => h (Fin.castAdd m i)))
      (ihb _ (fun i => h (Fin.natAdd n i)))

theorem annotated_repeated {k Γ} (p : Policy) (F : Variable Γ (Ty.curriedGround (k+1)))
    (site : MacroSite) (n : Nat) (q : OrdinalExpression Γ) (hq : Annotated p F q) :
    Annotated p F (AdmissibleAssignment.repeated p site n q) := by
  cases n with
  | zero => exact .free (by simp [AdmissibleAssignment.repeated, Active])
  | succ n => exact annotated_expand p F (p.shape site n) (fun _ => q) (fun _ => hq)

theorem headClosureTransport : Targets.HeadClosureTransport := by
  intro k Γ F p q hq
  induction hq with
  | free h => exact .free (fun ha => h ((active_headClosure F _).mp ha))
  | tracked => exact .tracked
  | add ha hb iha ihb => exact .add iha ihb
  | collapse op hs ht ih =>
    exact .collapse (GroundOperatorDischarge.Proof.operatorWitnessTransport Γ p _ op)
      (fun ha => (active_headClosure F _).mpr (hs ((active_headClosure F _).mp ha))) ih

end LogicLineages.OrdinalComparison.Source.ActiveScalarAnnotation.Proof
