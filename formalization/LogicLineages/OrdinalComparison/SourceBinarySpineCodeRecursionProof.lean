module
public import LogicLineages.OrdinalComparison.SourceBinarySpineCodeTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceBinarySpineCode.Proof
open SourcePlanSpineCode SourcePrimitiveForestCode

theorem fold_offset (bits : List Nat) (s : BinaryState) (n : Nat) :
    bits.foldl (fun s b => advance b s) (s.1+n,s.2)=
      let t := bits.foldl (fun s b => advance b s) s
      (t.1+n,t.2) := by
  induction bits generalizing s with
  | nil => rfl
  | cons b bits ih =>
    simp only [List.foldl_cons]
    have ha : advance b (s.1+n,s.2)=((advance b s).1+n,(advance b s).2) := by
      by_cases h : b=0 <;> simp [advance,h,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
    rw [ha,ih]

theorem build_nil (base out : Nat) (is : List Instruction) :
    buildBits [] base out is=terminal base out::is := rfl

theorem build_even (bits : List Nat) (base out : Nat) (is : List Instruction) :
    buildBits (0::bits) base out is=(4,0,0,0)::
      buildBits bits base 1 ((2,1,1,shiftPort 1 out)::SourcePlanInsertionCode.insert 0 1 is) := by
  simp only [buildBits,List.foldl_cons]
  rw [show advance 0 (0,out,is)=(1,1,(2,1,1,shiftPort 1 out)::SourcePlanInsertionCode.insert 0 1 is) from rfl]
  have h := fold_offset bits (0,1,(2,1,1,shiftPort 1 out)::SourcePlanInsertionCode.insert 0 1 is) 1
  simp only [Nat.zero_add] at h
  rw [h]
  rw [Nat.add_comm _ 1]
  simp [List.replicate_add,List.append_assoc]

theorem build_odd (b : Nat) (hb : b≠0) (bits : List Nat) (base out : Nat) (is : List Instruction) :
    buildBits (b::bits) base out is=(4,0,0,0)::(4,0,0,0)::(4,0,0,0)::
      buildBits bits base 3 ((2,3,3,2)::(3,1,0,0)::(2,2,1,shiftPort 3 out)::SourcePlanInsertionCode.insert 0 3 is) := by
  simp only [buildBits,List.foldl_cons]
  rw [show advance b (0,out,is)=(3,3,(2,3,3,2)::(3,1,0,0)::(2,2,1,shiftPort 3 out)::SourcePlanInsertionCode.insert 0 3 is) by simp [advance,hb]]
  have h := fold_offset bits (0,3,(2,3,3,2)::(3,1,0,0)::(2,2,1,shiftPort 3 out)::SourcePlanInsertionCode.insert 0 3 is) 3
  simp only [Nat.zero_add] at h
  rw [h]
  rw [Nat.add_comm _ 3]
  simp [List.replicate_add,List.append_assoc]
end LogicLineages.OrdinalComparison.Source.SourceBinarySpineCode.Proof
