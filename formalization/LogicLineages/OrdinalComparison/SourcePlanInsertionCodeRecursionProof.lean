module
public import LogicLineages.OrdinalComparison.SourcePlanInsertionCodeTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourcePlanInsertionCode.Proof
open SourcePlanSpineCode

theorem scan_acc (k : Nat) (is : List Instruction) (d : Nat) (acc : List Instruction) :
    (is.foldl (scanStep k) (d,acc)).2=(is.foldl (scanStep k) (d,[])).2++acc := by
  induction is generalizing d acc with
  | nil => rfl
  | cons i is ih =>
    simp only [List.foldl_cons,scanStep]
    rw [ih,ih (nextDepth d i) [instruction d k i]]
    simp only [List.append_assoc,List.singleton_append]

theorem insert_nil (d k : Nat) : insert d k []=[] := rfl
theorem insert_cons (d k : Nat) (i : Instruction) (is : List Instruction) :
    insert d k (i::is)=instruction d k i::insert (nextDepth d i) k is := by
  simp only [insert,List.foldl_cons,scanStep]
  rw [scan_acc]
  simp only [List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,List.singleton_append]

theorem exactProtectedRecursion : Targets.ExactProtectedRecursion := by
  refine ⟨insert_nil,insert_cons,?_,?_⟩
  · intro d k; simp [portInsert]
  · intro d k p hp
    constructor
    · intro h; simp [portInsert,show p≠0 by omega,h]
    · intro h; simp [portInsert,show p≠0 by omega,show ¬p-1<d by omega]
end LogicLineages.OrdinalComparison.Source.SourcePlanInsertionCode.Proof
