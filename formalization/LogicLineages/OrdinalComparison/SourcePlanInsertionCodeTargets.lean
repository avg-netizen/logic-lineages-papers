module
public import LogicLineages.OrdinalComparison.SourcePlanInsertionCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourcePlanInsertionCode.Targets
open SourcePlanSpineCode ExistentialPlan

def ExactProtectedRecursion : Prop :=
  (∀ d k,insert d k []=[]) ∧
  (∀ d k i is,insert d k (i::is)=instruction d k i::insert (nextDepth d i) k is) ∧
  (∀ d k,portInsert d k 0=0) ∧
  (∀ d k p,0<p → (p-1<d → portInsert d k p=p) ∧ (d≤p-1 → portInsert d k p=p+k))

def ExactSupportedInsertion : Prop := ∀ (Θ Δ Γ : List Ty) (q : Plan (Θ++Γ)),
  ParametricExistentialPlan.Supported q →
  insert Θ.length Δ.length (spine q)=
    spine (BinaryPlan.renamePlan (ContextInsertionCode.insertion Θ Δ Γ) q)

def UniformPrimitiveRecursive : Prop :=
  Primrec (fun p : Nat×Nat×Nat => portInsert p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : Nat×Nat×Instruction => instruction p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : Nat×Nat×List Instruction => insert p.1 p.2.1 p.2.2)
end LogicLineages.OrdinalComparison.Source.SourcePlanInsertionCode.Targets
