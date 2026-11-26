module
public import LogicLineages.StandardControlCurrent.PolicyConstructorsTargets
public import LogicLineages.StandardControlCurrent.PolicyShapeSyntaxProof
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxBoxProof

@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicyConstructorsSyntaxProof
open OrdinalComparison Source Source.AdmissibleSum Source.OrdinalSyntax PolicyConstructors

theorem constants : PolicyConstructorsTargets.ConstantCalibration := by
  refine ⟨?_,?_,?_,?_⟩
  · intro p Γ
    simp [onesCode,AdmissibleAssignment.assignment,vectorCode,typedCode,code,List.ofFn_const,List.replicate_succ]
  · intro p Γ
    simp [onesCode,AdmissibleAssignment.assignment,vectorCode,typedCode,code,List.ofFn_const,List.replicate_succ]
  · intro p Γ τ
    simp [onesCode,AdmissibleAssignment.assignment,vectorCode,typedCode,code,List.ofFn_const,List.replicate_succ]
  · intro p Γ σ
    have hn := PolicyShapeSyntaxProof.literal.2 p .numeral Γ 2 (.one : OrdinalExpression Γ)
    change PolicyShape.repeatCode p (PolicyShape.siteCode .numeral) 2 1 =
      some (typedCode (AdmissibleAssignment.numeral p 2 : OrdinalExpression Γ)) at hn
    simp only [recursorCode,hn,Option.bind_some,AdmissibleAssignment.assignment,Option.map_some]
    dsimp only
    congr 1
    apply List.ext_getElem
    · simp [vectorCode]
    · intro j hj hk
      simp only [List.getElem_map,List.getElem_range,vectorCode,List.getElem_ofFn]
      by_cases h0 : j=0 <;> by_cases h1 : j=σ.level+2 <;> simp [h0,h1,typedCode,code]

theorem tail : PolicyConstructorsTargets.TailCalibration := by
  intro p Γ n f g
  by_cases hn : n=0
  · simp [boxTailCode,AdmissibleAssignment.boxTail,hn,typedCode,code,node]
  · have hnum := PolicyShapeSyntaxProof.literal.2 p .numeral Γ n (.one : OrdinalExpression Γ)
    change PolicyShape.repeatCode p (PolicyShape.siteCode .numeral) n 1 =
      some (typedCode (AdmissibleAssignment.numeral p n : OrdinalExpression Γ)) at hnum
    simp only [boxTailCode,hn,if_false,hnum,Option.bind_some,AdmissibleAssignment.boxTail]
    have hm := PolicyShapeSyntaxProof.literal.1 p .optionalBoxTail Γ 2
      (fun i => if i.val=0 then f else if i.val=1 then g else AdmissibleAssignment.numeral p n)
    simpa [List.ofFn_succ,AdmissiblePartial.three] using hm

theorem application : PolicyConstructorsTargets.ApplicationCalibration := by
  intro p Γ σ τ f g
  have hf : (vectorCode f).getD 0 0 = typedCode (f 0) := by simp [vectorCode,List.getD_eq_getElem?_getD]
  have hg : (vectorCode g).getD 0 0 = typedCode (g 0) := by simp [vectorCode,List.getD_eq_getElem?_getD]
  simp only [PolicyConstructors.applicationCode,hf,hg]
  rw [tail p Γ σ.level (f 0) (g 0)]
  dsimp only
  congr 1
  apply List.ext_getElem
  · simp [vectorCode]
  · intro j hj hk
    simp only [List.getElem_map,List.getElem_range,vectorCode,List.getElem_ofFn]
    unfold AdmissibleAssignment.application AdmissibleAssignment.box
    by_cases hz : j=0
    · simp only [hz,if_true]
      have hp := ordinalSyntaxBoxPositiveCorrect Γ _ _ f g 1
      dsimp only [vectorCode] at hp
      rw [hp]
      simp [typedCode,code,node]
    · simp only [if_neg hz]
      exact ordinalSyntaxBoxPositiveCorrect Γ _ _ f g j
end LogicLineages.StandardControlCurrent.PolicyConstructorsSyntaxProof
