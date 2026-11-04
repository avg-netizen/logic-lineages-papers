module
public import LogicLineages.OrdinalComparison.SourceMachineConjunctionPlanTargets
public import LogicLineages.OrdinalComparison.ParametricScalingPlanProof
public import LogicLineages.OrdinalComparison.SourceMachineHaltingConjunctionProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceMachineConjunctionPlan.Proof
open PrimitiveLowering ExistentialPlan ParametricExistentialPlan ParametricSourceSuccessor
open SourceAdditionCompletion SourceSortCompletion

theorem successor_equation (G : Nat → Nat) (hm : StrictMono G) (hi : ∀ n,n ≤ G n)
    {Γ} (ρ : OrdinalComponent Γ → Nat) (x y : Variable Γ .ground) :
    ParametricSourceAddition.Equation G ρ (successorProbe x) (.var y) ↔ input ρ y=G (input ρ x+4) := by
  have hv := PrimitiveLowering.Proof.port_assignment (Atom.var y)
  have hd : denoteWith G (fun c => ((ρ c+1 : Nat) : Ordinal))
      (PrimitiveLowering.Proof.portExpression (Atom.var y)) = ((input ρ y+1 : Nat) : Ordinal) := rfl
  refine Iff.trans ?_ ((ParametricSourceSuccessor.Proof.genericSourceGraph G hm hi Γ x).2 ρ (input ρ y))
  constructor
  · rintro ⟨va,vb,ha,hb,he⟩
    cases Option.some.inj (hv.symm.trans hb)
    exact ⟨va,ha,he.trans hd⟩
  · rintro ⟨va,ha,he⟩
    exact ⟨va,_,ha,hv,he.trans hd.symm⟩

theorem graph_leaf (b : Nat) {Γ} (ρ : Variable Γ .ground → Nat)
    (x y : Variable Γ .ground) :
    ParametricSourceAddition.Equation (SourceMachineControlNonperiodicity.gamma b) (inputs ρ)
      (Expr.successor (.var x)).graph.term (Expr.port (.var y)).graph.term ↔
      ρ y=SourceMachineControlNonperiodicity.gamma b (ρ x+4) := by
  rw [(PrimitiveLowering.Proof.primitiveRealization Γ _).1,
    (PrimitiveLowering.Proof.primitiveRealization Γ _).1]
  have h := ParametricCoefficientOne.Proof.actualGammaCoefficientOne b
  exact successor_equation _ h.1 h.2.1 (inputs ρ) x y
end LogicLineages.OrdinalComparison.Source.SourceMachineConjunctionPlan.Proof
