import LogicLineages.PersistentMarking.NumberedWindowAtomicAddressTargets
import LogicLineages.PersistentMarking.NumberedWindowOuterShapeChecks
import LogicLineages.PersistentMarking.NumberedWindowDirectClassAddressChecks
import LogicLineages.PersistentMarking.NumberedWindowExternalAtomicClassesProof
import LogicLineages.PersistentMarking.NumberedWindowArithmeticLeastClassChecks
import LogicLineages.PersistentMarking.NumberedWindowPathWitnessClassCode
import LogicLineages.PersistentMarking.NumberedWindowExternalNeutralPrimaryProof
import LogicLineages.PersistentMarking.NumberedWindowArithmeticClassAddressProof

namespace LogicLineages.PersistentMarking.NumberedWindowAtomicAddressProof
open Spine NumberedWindowSyntax NumberedWindowSimulationData NumberedWindowPrimary
open NumberedWindowAtomicAddressTargets NumberedWindowOuterShape NumberedWindowOuterShapeTargets
open NumberedWindowOuterShapeChecks NumberedWindowDirectClassAddressTargets NumberedWindowDirectClassAddressChecks
open NumberedWindowArithmeticScalarTargets NumberedWindowArithmeticClassAddress NumberedWindowArithmeticClassAddressProof
open NumberedWindowArithmeticLeastClass NumberedWindowArithmeticLeastClassChecks NumberedWindowArithmeticTermCode
open NumberedWindowExternalAtomicClassesProof NumberedWindowExternalNeutralTargets
open NumberedWindowExternalNeutralPrimaryProof NumberedWindowExternalTypeFactsTargets
open NumberedWindowPathWitnessTargets NumberedWindowPathWitnessClassCode
open NumberedWindowApplicationDomainProof (annotation)

private theorem typedDirect {S : Signature} {K : List Ty} (hk : DecisionSourceUniverse.Closed K)
    {source cert target tag : Nat} (shape : outerShape (fixed S K) source = some tag)
    (edge : literalDirect S K source cert target = true) :
    ∃ (Γ : List Ty) (τ : Ty) (i j : Nat) (q r : Class S K (finiteC Γ) τ),
      encodeAddress ⟨Γ,τ,i⟩ = source ∧ encodeAddress ⟨Γ,τ,j⟩ = target ∧
        ActualCodeAt S K Γ τ i q ∧ ActualCodeAt S K Γ τ j r ∧ RepresentsTag q tag ∧ ClassEdge q r := by
  obtain ⟨Γ,τ,i,q,qNumber,hq,tags⟩ := (exact_OuterShape S K hk source tag).mp shape
  obtain ⟨Δ,ρ,m,j,p,r,pNumber,rNumber,hp,hr,step⟩ :=
    (exact_DirectClassAddress S K hk source target).mp ⟨cert,edge⟩
  have same : (⟨Γ,τ,i⟩ : ClassAddress) = ⟨Δ,ρ,m⟩ :=
    Option.some.inj ((atCode qNumber).symm.trans (atCode pNumber))
  injection same with ctx type code
  subst Δ
  subst ρ
  subst m
  have sameClass : p = q := NumberedWindowPathWitnessClassCode.sameClass hk hp hq
  subst p
  exact ⟨Γ,τ,i,j,q,r,qNumber,rNumber,hq,hr,tags,step⟩

private theorem bottomFromTag {S K C τ} (Q : WindowCarrier S K C τ)
    (htag : literalTag Q.val = 3) : Q.val = .bottom τ := by
  cases shape : Q.val <;> simp [literalTag,shape] at htag
  case bottom υ =>
    have same : υ = τ := by simpa [shape,NTerm.type] using annotation Q.property.1
    exact congrArg NTerm.bottom same

private theorem variableFromTag {S K C τ tag} (Q : WindowCarrier S K C τ)
    (allowed : tag = 0 ∨ tag = 1) (htag : literalTag Q.val = tag) :
    ∃ i, Q.val = .free τ i ∨ Q.val = .bound τ i := by
  rcases allowed with h | h
  · have freeTag : literalTag Q.val = 0 := htag.trans h
    cases shape : Q.val <;> simp [literalTag,shape] at freeTag
    case free σ i =>
      have eq : σ = τ := by simpa [shape,NTerm.type] using annotation Q.property.1
      exact ⟨i,Or.inl (congrArg (fun (t : Ty) => NTerm.free t i) eq)⟩
  · have boundTag : literalTag Q.val = 1 := htag.trans h
    cases shape : Q.val <;> simp [literalTag,shape] at boundTag
    case bound σ i =>
      have eq : σ = τ := by simpa [shape,NTerm.type] using annotation Q.property.1
      exact ⟨i,Or.inr (congrArg (fun (t : Ty) => NTerm.bound t i) eq)⟩

private def bottomView : NTerm → Option Ty
  | .bottom τ => some τ
  | _ => none

private theorem primaryView {S K C τ Q R} (h : Primary S K C τ Q R) :
    bottomView Q = bottomView R := by
  induction h using Primary.rec (motive_2 := fun _ _ _ _ _ => True) with
  | symm _ eq => exact eq.symm
  | trans _ _ left right => exact left.trans right
  | _ => first | rfl | trivial

private theorem bottomRigid {S K C τ Q R}
    (h : Primary S K C τ Q R) (bottom : Q = .bottom τ) : R = .bottom τ := by
  have view : bottomView R = some τ := by simpa only [bottom,bottomView] using (primaryView h).symm
  cases R <;> simp_all [bottomView]

private theorem canonicalBottom {S : Signature} {K Γ : List Ty} {τ : Ty}
    (hk : DecisionSourceUniverse.Closed K) {r : Class S K (finiteC Γ) τ} {j : Nat}
    (hr : ActualCodeAt S K Γ τ j r) (bottom : ClassBottom r) :
    j = encodeTerm (.bottom τ) ∧ RepresentsTag r 3 := by
  obtain ⟨B,hB,bclass⟩ := bottom
  have known := atRep hk B bclass hr
  obtain ⟨n,R,least,_,code,_,related,_,_⟩ :=
    exact_LeastCodeSpecification S K Γ τ B.val hk B.property
  have bottomR := bottomRigid related hB
  have eq : j = n := Option.some.inj (known.symm.trans least)
  refine ⟨eq.trans (code.symm.trans (congrArg encodeTerm bottomR)),?_⟩
  intro P pclass
  have primary := primaryOfClassEquality B P (bclass.trans pclass.symm)
  simp only [bottomRigid primary hB,literalTag]

theorem noBottom : NoBottomDirectAddress := by
  intro S K hk source cert target shape
  apply Bool.eq_false_iff.mpr
  intro edge
  obtain ⟨Γ,τ,i,j,q,r,_,_,hq,_,tags,step⟩ := typedDirect hk shape edge
  obtain ⟨Q,classQ,_⟩ := hq
  exact bottomNoEdge ⟨Q,bottomFromTag Q (tags Q classQ),classQ⟩ step

theorem variableEdgeAddress : ExactVariableDirectAddress := by
  intro S K hk source cert target tag allowed shape edge
  obtain ⟨Γ,τ,i,j,q,r,sourceCode,targetCode,hq,hr,tags,step⟩ := typedDirect hk shape edge
  obtain ⟨Q,classQ,_⟩ := hq
  have isVariable : VariableClass q := ⟨Q,variableFromTag Q allowed (tags Q classQ),classQ⟩
  obtain ⟨code,allTags⟩ := canonicalBottom hk hr (variableEdge isVariable step)
  have exactTarget : target = encodeAddress ⟨Γ,τ,encodeTerm (.bottom τ)⟩ := by
    rw [← code]
    exact targetCode.symm
  exact ⟨Γ,τ,i,sourceCode,exactTarget,
    (exact_OuterShape S K hk target 3).mpr ⟨Γ,τ,j,r,targetCode,hr,allTags⟩⟩

end LogicLineages.PersistentMarking.NumberedWindowAtomicAddressProof
