module
public import LogicLineages.OrdinalComparison.SourceMachineConjunctionPlanTargets
public import LogicLineages.OrdinalComparison.ParametricScalingPlanSizeProof
public import LogicLineages.OrdinalComparison.ParametricBinaryPlanProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceMachineConjunctionPlan.Proof
open PrimitiveLowering ExistentialPlan BinaryPlan ParametricScalingPlan

private theorem tail_size (e : Nat) :
    (tail e).vertices=80*(e+8)+4 ∧ (tail e).equations=10*(e+8)+1 ∧
    (tail e).witnesses=10*e+72 := by
  let rest : Plan Wired :=
    .gate (.add (port 10) (port 7) (port 3))
      (.gate (.eq (port 3) (port 2))
        (.gate (.add (port 12) (port 12) (port 4))
          (.gate (.add (port 4) (port 6) (port 5))
            (.gate (.eq (port 11) (port 5))
              (.equation (Expr.successor (port 10)).graph (Expr.port (port 11)).graph .done)))))
  have h := ParametricScalingPlan.Proof.plan_size e (port 1) (port 2) rest
  have hv : rest.vertices=404 := by rfl
  have he : rest.equations=51 := by rfl
  have hw : rest.witnesses=45 := by rfl
  rw [hv,he,hw] at h
  change 80+(80+(scalePlan e (port 1) (port 2) rest).vertices)=_ ∧
    10+(10+(scalePlan e (port 1) (port 2) rest).equations)=_ ∧
    9+(9+(scalePlan e (port 1) (port 2) rest).witnesses)=_
  omega

theorem plan_bounds (b e : Nat) :
    (plan b e).vertices ≤ 80*(e+4*bits b+27)+4 ∧
    (plan b e).equations ≤ 10*(e+4*bits b+27)+1 ∧
    (plan b e).witnesses ≤ 10*e+40*bits b+268 := by
  let q : Plan (List.replicate 7 Ty.ground) :=
    .existsGround (.existsGround (.existsGround
      (.existsGround (.existsGround (.existsGround (tail e))))))
  have ht := tail_size e
  have hq : q.vertices=(tail e).vertices ∧ q.equations=(tail e).equations ∧
      q.witnesses=(tail e).witnesses+6 := by
    refine ⟨rfl,rfl,?_⟩
    change 1+(1+(1+(1+(1+(1+(tail e).witnesses)))))=(tail e).witnesses+6
    omega
  let q1 : Plan (List.replicate 6 Ty.ground) := constantPlan 1 q
  let q4 : Plan (List.replicate 5 Ty.ground) := constantPlan 4 q1
  let qc : Plan Base := constantPlan (SourceMachineHaltingConjunction.oddConstant b) q4
  have h1 := BinaryPlan.Proof.literalSize (List.replicate 6 Ty.ground) 1 q
  have h4 := BinaryPlan.Proof.literalSize (List.replicate 5 Ty.ground) 4 q1
  have hc := BinaryPlan.Proof.literalSize Base (SourceMachineHaltingConjunction.oddConstant b) q4
  have hl1 : Nat.log2 1=0 := by decide
  have hl4 : Nat.log2 4=2 := by decide
  rw [hl1] at h1
  rw [hl4] at h4
  change q1.vertices ≤ 400+q.vertices ∧ q1.equations ≤ 50+q.equations ∧ q1.witnesses ≤ 50+q.witnesses at h1
  change q4.vertices ≤ 1040+q1.vertices ∧ q4.equations ≤ 130+q1.equations ∧ q4.witnesses ≤ 130+q1.witnesses at h4
  change qc.vertices ≤ 80*(4*bits b+1)+q4.vertices ∧ qc.equations ≤ 10*(4*bits b+1)+q4.equations ∧ qc.witnesses ≤ 40*bits b+10+q4.witnesses at hc
  change qc.vertices ≤ _ ∧ qc.equations ≤ _ ∧ qc.witnesses ≤ _
  omega

theorem exactCompiledBounds : Targets.ExactCompiledBounds := by
  intro b e
  have hp := plan_bounds b e
  have hc := ExistentialPlan.Proof.size Base (plan b e)
  have hb : Base.length=4 := rfl
  rw [hb] at hc
  exact ⟨hc.1.trans hp.1,by omega,by omega⟩
end LogicLineages.OrdinalComparison.Source.SourceMachineConjunctionPlan.Proof
