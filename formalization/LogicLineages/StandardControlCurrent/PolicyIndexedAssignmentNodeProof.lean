module
public import LogicLineages.StandardControlCurrent.PolicyIndexedAssignmentTargets
import LogicLineages.StandardControlCurrent.PolicyIndexedShapeProof

@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicyIndexedAssignment
open OrdinalComparison Source Source.AdmissibleSum Source.SyntaxCode Source.OrdinalSyntax
open Nat.Partrec (Code)

private theorem childrenDecrease (s t : Node) (ht : t ∈ children s) : rank t < rank s := by
  by_cases h5 : s.2%8=5
  · have hd := Nat.div_lt_self (by omega : 0<s.2) (by decide : 1<8)
    simp only [children,if_pos h5,List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl | rfl
    · exact (Nat.unpair_left_le _).trans_lt hd
    · exact (Nat.unpair_right_le _).trans_lt hd
  · by_cases h6 : s.2%8=6
    · have hd := Nat.div_lt_self (by omega : 0<s.2) (by decide : 1<8)
      simp only [children,if_neg h5,if_pos h6,List.mem_singleton] at ht
      subst t
      exact (Nat.unpair_right_le _).trans_lt hd
    · simp [children,h5,h6] at ht

private theorem typedLiteral (p : Policy) (s : Node) :
    typedNode p s ((children s).map (fun q => PolicyAssignment.assignmentCode p q.1 q.2)) =
      some (PolicyAssignment.assignmentCode p s.1 s.2) := by
  rcases s with ⟨ctx,n⟩
  conv_rhs => rw [PolicyAssignment.assignmentCode]
  cases hn : check ctx n with
  | none => simp [typedNode,body,hn]
  | some ty =>
    by_cases h : n%8 < 5
    · simp [typedNode,body,hn,h,PolicyAssignment.primeCode]
    · by_cases h5 : n%8=5
      · cases harg : check ctx (n/8).unpair.2 <;>
          cases hleft : PolicyAssignment.assignmentCode p ctx (n/8).unpair.1 <;>
          cases hright : PolicyAssignment.assignmentCode p ctx (n/8).unpair.2 <;>
          simp [typedNode,body,hn,h,h5,children,harg,hleft,hright]
      · by_cases h6 : n%8=6
        · cases hb : check ((n/8).unpair.1::ctx) (n/8).unpair.2 <;>
            cases hr : PolicyAssignment.assignmentCode p ((n/8).unpair.1::ctx) (n/8).unpair.2 <;>
            simp [typedNode,body,hn,h,h5,h6,children,hb,hr]
        · simp [typedNode,body,hn,h,h5,h6]

private theorem numeralLiteral (c : Code) (p : Policy) (hc : PolicyIndexedShape.Implements c p)
    (n : Nat) : numeral c n = Part.some (PolicyShape.repeatCode p (PolicyShape.siteCode .numeral) n 1) := by
  by_cases hn : n=0
  · simp [numeral,PolicyShape.repeatCode,hn]
  · simp [numeral,PolicyShape.repeatCode,hn,PolicyIndexedShape.exactPolicyIndexedShape c p hc]

private theorem tailLiteral (c : Code) (p : Policy) (hc : PolicyIndexedShape.Implements c p)
    (n f g : Nat) :
    tailCode c n f g = Part.some (PolicyConstructors.boxTailCode p n f g) := by
  by_cases hn : n=0
  · simp [tailCode,PolicyConstructors.boxTailCode,hn]
  · simp only [tailCode,PolicyConstructors.boxTailCode,if_neg hn,numeralLiteral c p hc,Part.bind_some]
    cases h : PolicyShape.repeatCode p (PolicyShape.siteCode .numeral) n 1 <;>
      simp [PolicyIndexedShape.exactPolicyIndexedShape c p hc]

private theorem recLiteral (c : Code) (p : Policy) (hc : PolicyIndexedShape.Implements c p)
    (i r : Nat) :
    (numeral c 2).map (Option.map (recursorFrom i r)) =
      Part.some (PolicyConstructors.recursorCode p i r) := by
  rw [numeralLiteral c p hc]
  unfold PolicyConstructors.recursorCode
  cases PolicyShape.repeatCode p (PolicyShape.siteCode .numeral) 2 1 <;> rfl

private theorem appLiteral (c : Code) (p : Policy) (hc : PolicyIndexedShape.Implements c p)
    (r i : Nat) (f g : List Nat) :
    (tailCode c i (f.getD 0 0) (g.getD 0 0)).map (Option.map (applicationFrom r i f g)) =
      Part.some (PolicyConstructors.applicationCode p r i f g) := by
  rw [tailLiteral c p hc]
  unfold PolicyConstructors.applicationCode
  cases PolicyConstructors.boxTailCode p i (f.getD 0 0) (g.getD 0 0) <;> rfl

private theorem bodyLiteral (backend : Abstraction) (c : Code) (p : Policy)
    (hc : PolicyIndexedShape.Implements c p) (hb : ImplementsAbstraction backend c p)
    (s : Node) (rs : List Value) :
    assemble backend c (s,rs) = Part.some (typedNode p s rs) := by
  rcases s with ⟨ctx,n⟩
  unfold assemble typedNode body
  simp only
  cases hn : check ctx n with
  | none => simp [hn]
  | some ty =>
    by_cases h : n%8<5
    · by_cases h0 : n%8=0
      · simp [hn,h,h0]
      · by_cases h4 : n%8=4 <;> simp [hn,h,h0,h4,recLiteral c p hc]
    · by_cases h5 : n%8=5
      · cases harg : check ctx (n/8).unpair.2 <;>
          cases hf : rs.getD 0 none <;> cases hg : rs.getD 1 none <;>
          simp [hn,h,h5,harg,hf,hg]
        rename_i arg f g
        change Part.map some (Part.map (Option.map (applicationFrom (typeLevel ty) (typeLevel arg) f g))
          (tailCode c (typeLevel arg) (f.getD 0 0) (g.getD 0 0))) =
            Part.some (some (PolicyConstructors.applicationCode p (typeLevel ty) (typeLevel arg) f g))
        rw [appLiteral c p hc] <;> rfl
      · by_cases h6 : n%8=6
        · cases hty : check ((n/8).unpair.1::ctx) (n/8).unpair.2 <;>
            cases hval : rs.getD 0 none <;>
            simp [hn,h,h5,h6,hty,hval]
          rename_i bodyType value
          rw [hb (typeLevel (n/8).unpair.1) (typeLevel bodyType) value] <;> rfl
        · simp [hn,h,h5,h6]

theorem exactIndexedAssignmentNode : ExactIndexedAssignmentNode :=
  ⟨childrenDecrease,typedLiteral,bodyLiteral⟩

end LogicLineages.StandardControlCurrent.PolicyIndexedAssignment
