import LogicLineages.PersistentMarking.DecisionObservationTargets
import LogicLineages.PersistentMarking.DecisionPortsProof
import LogicLineages.PersistentMarking.SpineSubstitutionProof
namespace LogicLineages.PersistentMarking.DecisionAssignmentProof
open Spine NameBridge DecisionInventory DecisionPorts DecisionObservations

theorem enumeration (V : List Name) (Γ : Context) (stack : List Ty) (vs : Args) :
    vs ∈ assignments V Γ stack ↔ Assignment V Γ stack vs := by
  induction stack generalizing vs with
  | nil =>
    constructor
    · intro h; simp only [assignments,List.mem_singleton] at h; subst vs; exact .nil
    · intro h; cases h; simp [assignments]
  | cons σ stack ih =>
    constructor
    · intro h
      obtain ⟨q,hq,hs⟩ := List.mem_flatMap.mp h
      obtain ⟨qs,hqs,rfl⟩ := List.mem_map.mp hs
      exact .cons ((DecisionPortsProof.valuesExact V Γ σ q).mp hq) ((ih qs).mp hqs)
    · intro h; cases h with
      | cons hq hqs => exact List.mem_flatMap.mpr ⟨_,(DecisionPortsProof.valuesExact V Γ _ _).mpr hq,List.mem_map.mpr ⟨_,(ih _).mpr hqs,rfl⟩⟩
theorem typed (V : List Name) (Γ : Context) (stack : List Ty) (vs : Args) (h : Assignment V Γ stack vs) :
    BaseTyped EmptyContext vs stack := by
  induction h with
  | nil => exact .nil
  | cons hq hqs ih =>
    obtain ⟨i,hi,rfl⟩ := hq
    exact .cons .free ih
theorem length (V : List Name) (Γ : Context) (stack : List Ty) (vs : Args) (h : Assignment V Γ stack vs) :
    vs.length = stack.length := by
  induction h with
  | nil => rfl
  | cons hq hqs ih => simp only [Args.length,List.length_cons,ih]; omega
theorem openingTyped (V : List Name) (Γ : Context) (stack : List Ty) (vs : Args) (q : Expr) (τ : Ty)
    (h : Assignment V Γ stack vs) (ht : Typed (BoundContext.prefix stack EmptyContext) q τ) :
    Typed EmptyContext (openOccurrence vs q) τ :=
  SpineSubstitutionProof.parallelPreserves EmptyContext stack vs q τ (typed V Γ stack vs h) ht

def FreeValues (vs : Args) : Prop := ∀ i v, vs.get i = some v → ∃ σ x, v = Expr.free σ x

theorem freeValues (V : List Name) (Γ : Context) (stack : List Ty) (vs : Args) (h : Assignment V Γ stack vs) : FreeValues vs := by
  induction h with
  | nil => intro i v hv; cases i <;> cases hv
  | cons hq hqs ih =>
    intro i v hv
    cases i with
    | zero =>
      simp only [Args.get,Option.some.injEq] at hv
      subst v
      obtain ⟨i,hi,rfl⟩ := hq
      exact ⟨_,_,rfl⟩
    | succ i => exact ih i v hv

mutual
 theorem subFacts (vs : Args) (hv : FreeValues vs) (d : Nat) (q : Expr) :
    lambdaDepth (substitute vs d q) = lambdaDepth q ∧
    (Ordinary q → Ordinary (substitute vs d q)) ∧
    (∀ S, Valid S q → Valid S (substitute vs d q)) := by
  cases q with
  | free σ x => exact ⟨rfl,id,fun _ => id⟩
  | bound σ i =>
    by_cases hi : i < d
    · simp only [substitute,if_pos hi]; exact ⟨rfl,id,fun _ => id⟩
    · cases hl : vs.get (i-d) with
      | none => simp only [substitute,if_neg hi,hl]; exact ⟨rfl,id,fun _ => id⟩
      | some v =>
        obtain ⟨τ,x,rfl⟩ := hv (i-d) v hl
        simp only [substitute,if_neg hi,hl,shift]
        exact ⟨rfl,fun _ => trivial,fun _ _ => trivial⟩
  | lam σ q =>
    obtain ⟨hd,ho,hvalid⟩ := subFacts vs hv (d+1) q
    exact ⟨by simp only [substitute,lambdaDepth,hd],ho,hvalid⟩
  | head f bs =>
    obtain ⟨hd,ho,hvalid⟩ := subFactsArgs vs hv d bs
    exact ⟨hd,ho,fun S h => ⟨h.1,hvalid S h.2⟩⟩
  | marked f τ bs es =>
    obtain ⟨hd,ho,hvalid⟩ := subFactsArgs vs hv d bs
    obtain ⟨hd',ho',hvalid'⟩ := subFactsArgs vs hv d es
    exact ⟨by simp only [substitute,lambdaDepth,hd,hd'],fun h => False.elim h,fun S h => ⟨h.1,hvalid S h.2.1,hvalid' S h.2.2⟩⟩
 termination_by sizeOf q
 theorem subFactsArgs (vs : Args) (hv : FreeValues vs) (d : Nat) (qs : Args) :
    lambdaDepthArgs (substituteArgs vs d qs) = lambdaDepthArgs qs ∧
    (OrdinaryArgs qs → OrdinaryArgs (substituteArgs vs d qs)) ∧
    (∀ S, ValidArgs S qs → ValidArgs S (substituteArgs vs d qs)) := by
  cases qs with
  | nil => exact ⟨rfl,id,fun _ => id⟩
  | cons q qs =>
    obtain ⟨hd,ho,hvalid⟩ := subFacts vs hv d q
    obtain ⟨hd',ho',hvalid'⟩ := subFactsArgs vs hv d qs
    exact ⟨by simp only [substituteArgs,lambdaDepthArgs,hd,hd'],fun h => ⟨ho h.1,ho' h.2⟩,fun S h => ⟨hvalid S h.1,hvalid' S h.2⟩⟩
 termination_by sizeOf qs
end

theorem openingDepth (V : List Name) (Γ : Context) (stack : List Ty) (vs : Args) (q : Expr)
    (h : Assignment V Γ stack vs) : lambdaDepth (openOccurrence vs q) = lambdaDepth q :=
  (subFacts vs (freeValues V Γ stack vs h) 0 q).1
end LogicLineages.PersistentMarking.DecisionAssignmentProof
