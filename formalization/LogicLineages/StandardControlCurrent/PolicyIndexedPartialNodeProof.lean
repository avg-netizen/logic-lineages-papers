module
public import LogicLineages.StandardControlCurrent.PolicyIndexedPartialTargets
import LogicLineages.StandardControlCurrent.PolicyIndexedMergeProof

@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicyIndexedPartial
open OrdinalComparison Source Source.AdmissibleSum Source.OrdinalSyntax
open Nat.Partrec (Code)

private theorem childrenDecrease (s c : Node) (hc : c ∈ children s) : rank c < rank s := by
  by_cases h : active s.2.2
  · have pos : 0 < s.2.2 := by rcases h with h | h | h <;> omega
    have hd := Nat.div_lt_self pos (show 1 < 8 by decide)
    simp only [children,if_pos h,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl
    · exact (Nat.unpair_left_le _).trans_lt hd
    · exact (Nat.unpair_right_le _).trans_lt hd
  · simp [children,h] at hc

private theorem typedLiteral (p : Policy) (s : Node) :
    typedNode p s ((children s).map (fun q => PolicyPartial.run p q.1 q.2.1 q.2.2)) =
      some (PolicyPartial.run p s.1 s.2.1 s.2.2) := by
  rcases s with ⟨level,i,n⟩
  conv_rhs => rw [PolicyPartial.run]
  by_cases hf : headFree n = true
  · simp [typedNode,caseBody,hf]
  · by_cases h3 : n%8=3
    · simp [typedNode,caseBody,hf,h3]
    · by_cases h4 : n%8=4
      · have h5 : n%8 ≠ 5 := by omega
        have h6 : n%8 ≠ 6 := by omega
        simp [typedNode,caseBody,children,active,typedMerge,childPair,hf,h3,h4,h5,h6,
          Option.bind_assoc]
      · by_cases h5 : n%8=5
        · have h6 : n%8 ≠ 6 := by omega
          by_cases hi : 0 < i <;>
            simp [typedNode,caseBody,children,active,typedMerge,childPair,hf,h3,h4,h5,h6,hi,
              Option.bind_assoc]
        · by_cases h6 : n%8=6
          · by_cases hi : i = 0
            · simp [typedNode,caseBody,children,active,collapse,childPair,hf,h3,h4,h5,h6,hi,
                Option.bind_assoc,Option.map]
              cases PolicyPartial.run p level 1 (Nat.unpair (n / 8)).1 <;>
                cases PolicyPartial.run p level 0 (Nat.unpair (n / 8)).2 <;> rfl
            · simp [typedNode,caseBody,children,active,collapse,childPair,hf,h3,h4,h5,h6,hi,
                Option.bind_assoc,Option.map]
          · simp [typedNode,caseBody,children,active,hf,h3,h4,h5,h6]

private theorem indexedMergeLiteral (c : Code) (p : Policy) (h : PolicyIndexedShape.Implements c p)
    (level tag : Nat) (xs : List Value) :
    indexedMerge c level tag xs = Part.some (typedMerge p level tag xs) := by
  unfold indexedMerge typedMerge
  cases hc : childPair xs with
  | none => rfl
  | some ab => exact PolicyIndexedMerge.mergeExact c p h level tag ab.1 ab.2

private theorem nodeLiteral (c : Code) (p : Policy) (h : PolicyIndexedShape.Implements c p)
    (s : Node) (xs : List Value) :
    assemble c (s,xs) = Part.some (typedNode p s xs) := by
  unfold assemble typedNode caseBody
  by_cases hf : headFree s.2.2 = true
  · simp [hf]
  · by_cases h3 : s.2.2%8=3
    · by_cases hi : s.2.1=(s.2.2/8).unpair.2 <;> simp [hf,h3,hi]
    · by_cases ha : active s.2.2
      · by_cases h4 : s.2.2%8=4
        · simp [hf,h3,ha,h4,indexedMergeLiteral c p h]
        · by_cases h5 : s.2.2%8=5
          · by_cases hi : 0 < s.2.1 <;> simp [hf,h3,ha,h4,h5,hi,indexedMergeLiteral c p h]
          · by_cases hi : s.2.1=0 <;> simp [hf,h3,ha,h4,h5,hi]
      · simp [hf,h3,ha]

theorem exactIndexedPartialNode : ExactIndexedPartialNode :=
  ⟨childrenDecrease,typedLiteral,nodeLiteral⟩

end LogicLineages.StandardControlCurrent.PolicyIndexedPartial
