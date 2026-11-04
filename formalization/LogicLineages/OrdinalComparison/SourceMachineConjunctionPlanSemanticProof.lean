module
public import LogicLineages.OrdinalComparison.SourceMachineConjunctionPlanLeafProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceMachineConjunctionPlan.Proof
open PrimitiveLowering ExistentialPlan BinaryPlan ParametricExistentialPlan ParametricScalingPlan

theorem supportedSyntax : Targets.SupportedSyntax := by
  intro b e
  simp only [plan,constantPlan,Supported,ParametricBinaryPlan.Proof.binary_supported]
  simp only [tail,Supported,ParametricPrimitiveLowering.Supported,true_and]
  apply (ParametricScalingPlan.Proof.scale_supported e (port 1) (port 2) _).mpr
  simp only [Supported,ParametricPrimitiveLowering.Supported,true_and]

private theorem tail_value (b e : Nat) (ν : Variable Wired .ground → Nat) :
    EvalWith (SourceMachineControlNonperiodicity.gamma b) ν (tail e) ↔
    ν (wire 9)+ν (wire 9)=ν (wire 0) ∧ ν (wire 0)+ν (wire 8)=ν (wire 1) ∧
    ν (wire 2)=2^e*ν (wire 1) ∧ ν (wire 10)+ν (wire 7)=ν (wire 3) ∧
    ν (wire 3)=ν (wire 2) ∧ ν (wire 12)+ν (wire 12)=ν (wire 4) ∧
    ν (wire 4)+ν (wire 6)=ν (wire 5) ∧ ν (wire 11)=ν (wire 5) ∧
    ν (wire 11)=SourceMachineControlNonperiodicity.gamma b (ν (wire 10)+4) := by
  simp only [tail,EvalWith,Gate.Holds]
  rw [ParametricScalingPlan.Proof.scale_correct]
  simp only [EvalWith,Gate.Holds,port,graph_leaf,and_true]
  rfl

theorem exactConjunction : Targets.ExactConjunction := by
  intro b e ρ
  simp only [plan,ParametricBinaryPlan.Proof.literal_correct,EvalWith]
  trans (∃ odd ww zp n s d : Nat,
    ρ (original 0)+ρ (original 0)=d ∧ d+SourceMachineHaltingConjunction.oddConstant b=s ∧
    n=2^e*s ∧ ρ (original 1)+4=zp ∧ zp=n ∧
    ρ (original 3)+ρ (original 3)=ww ∧ ww+1=odd ∧
    ρ (original 2)=odd ∧ ρ (original 2)=SourceMachineControlNonperiodicity.gamma b (ρ (original 1)+4))
  · apply exists_congr
    intro odd
    apply exists_congr
    intro ww
    apply exists_congr
    intro zp
    apply exists_congr
    intro n
    apply exists_congr
    intro s
    apply exists_congr
    intro d
    exact tail_value b e _
  ·
    constructor
    · rintro ⟨odd,ww,zp,n,s,d,hd,hs,hn,hzp,hzn,hww,hodd,hy,hg⟩
      refine ⟨?_,hg,by omega⟩
      change ρ (original 1)+4=2^e*(2*ρ (original 0)+SourceMachineHaltingConjunction.oddConstant b)
      calc
        ρ (original 1)+4 = zp := hzp
        _ = n := hzn
        _ = 2^e*s := hn
        _ = 2^e*(2*ρ (original 0)+SourceMachineHaltingConjunction.oddConstant b) := by
          congr 1
          omega
    · rintro ⟨hn,hg,hy⟩
      refine ⟨ρ (original 3)+ρ (original 3)+1,ρ (original 3)+ρ (original 3),
        ρ (original 1)+4,2^e*(2*ρ (original 0)+SourceMachineHaltingConjunction.oddConstant b),
        2*ρ (original 0)+SourceMachineHaltingConjunction.oddConstant b,
        ρ (original 0)+ρ (original 0),rfl,by omega,rfl,rfl,hn,rfl,rfl,hy,hg⟩
end LogicLineages.OrdinalComparison.Source.SourceMachineConjunctionPlan.Proof
