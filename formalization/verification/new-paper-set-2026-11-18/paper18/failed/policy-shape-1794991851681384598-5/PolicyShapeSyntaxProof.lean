module
public import LogicLineages.StandardControlCurrent.PolicyShapeTargets
public import Mathlib.Data.List.OfFn

@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicyShapeSyntaxProof
open OrdinalComparison Source Source.AdmissibleSum Source.OrdinalSyntax PolicyShape

theorem sites : PolicyShapeTargets.Sites := by intro s; cases s <;> rfl

theorem framed : PolicyShapeTargets.FramedExpansion := by
  intro Γ n s
  induction s with
  | leaf => intro xs rest stack; simp [shapeCode,run,step,expand]
  | @join n m a b iha ihb =>
    intro xs rest stack
    have hl := iha (fun i => xs (Fin.castAdd m i))
      (List.ofFn (fun i => typedCode (xs (Fin.natAdd n i))) ++ rest) stack
    have hr := ihb (fun i => xs (Fin.natAdd n i)) rest
      (typedCode (expand a (fun i => xs (Fin.castAdd m i)))::stack)
    simp only [shapeCode,run,List.foldl_append]
    rw [List.ofFn_add,List.append_assoc]
    change run [true] (run (shapeCode b) (run (shapeCode a)
      (some (List.ofFn (fun i => typedCode (xs (Fin.castAdd m i))) ++
        (List.ofFn (fun i => typedCode (xs (Fin.natAdd n i))) ++ rest), stack)))) = _
    rw [hl]
    rw [hr]
    rfl

theorem literal : PolicyShapeTargets.LiteralCalibration := by
  have hm : ∀ (p : Policy) (site : MacroSite) (Γ : List Ty) (n : Nat)
      (xs : Fin (n+1) → OrdinalExpression Γ),
      macroCode p (siteCode site) n (List.ofFn (fun i => typedCode (xs i))) =
        some (typedCode (expand (p.shape site n) xs)) := by
    intro p site Γ n xs
    unfold macroCode selector expandCode
    rw [sites]
    have h := framed Γ (n+1) (p.shape site n) xs [] []
    simp only [List.append_nil] at h
    rw [h]
    rfl
  refine ⟨hm,?_⟩
  intro p site Γ count t
  cases count with
  | zero => rfl
  | succ n =>
    simpa only [PolicyShape.repeatCode, Nat.add_one_ne_zero, if_false,
      Nat.add_sub_cancel, AdmissibleAssignment.repeated, List.ofFn_const] using
      hm p site Γ n (fun _ => t)
end LogicLineages.StandardControlCurrent.PolicyShapeSyntaxProof
