module
public import LogicLineages.OrdinalComparison.SourceMachineAggregateBridgeTargets
public import LogicLineages.OrdinalComparison.SourceMachinePlanFiniteProof
public import LogicLineages.OrdinalComparison.SourceGammaAggregateProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceMachineAggregateBridge.Proof
open ExistentialPlan ParametricExistentialPlan ParametricSourceEraser ParametricPrimitiveFinite

theorem equations_holds (b e : Nat)
    (ρ : Variable (compile (SourceMachineConjunctionPlan.plan b e)).context .ground → Nat) :
    (∀ f ∈ sources b e, ParametricSourceAddition.Equation
      (SourceMachineControlNonperiodicity.gamma b) (inputs ρ) f.1 f.2) ↔
    HoldsWith (SourceMachineControlNonperiodicity.gamma b)
      (compile (SourceMachineConjunctionPlan.plan b e)) ρ := by
  constructor
  · intro h f hf
    exact h (f.1.term,f.2.term) (List.mem_map.mpr ⟨f,hf,rfl⟩)
  · intro h f hf
    obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hf
    exact h g hg

theorem pointwiseAggregate : Targets.PointwiseAggregate := by
  intro b e ρ
  obtain ⟨l,r,hl,hr,hle,heq,hgap⟩ := SourceGammaAggregate.Proof.naturalEquationAggregate b _
    (inputs ρ) (sources b e) (SourceMachinePlanFinite.Proof.actualGammaForest b e ρ)
  exact ⟨l,r,hl,hr,hle,heq.trans (equations_holds b e ρ),
    fun hn => hgap (fun h => hn ((equations_holds b e ρ).mp h))⟩

theorem equal_iff_holds (b e : Nat)
    (ρ : Variable (compile (SourceMachineConjunctionPlan.plan b e)).context .ground → Nat) :
    SourceGammaAggregate.Equal (SourceMachineControlNonperiodicity.gamma b) (positive (inputs ρ))
      (aggregate b e).1 (aggregate b e).2 ↔
    HoldsWith (SourceMachineControlNonperiodicity.gamma b)
      (compile (SourceMachineConjunctionPlan.plan b e)) ρ := by
  obtain ⟨l,r,hl,hr,_,heq,_⟩ := pointwiseAggregate b e ρ
  exact (SourceGammaAggregate.Proof.equal_iff _ _ _ _ l r hl hr).trans heq

theorem strict_iff_not_holds (b e : Nat)
    (ρ : Variable (compile (SourceMachineConjunctionPlan.plan b e)).context .ground → Nat) :
    StrictAt b e ρ ↔ ¬ HoldsWith (SourceMachineControlNonperiodicity.gamma b)
      (compile (SourceMachineConjunctionPlan.plan b e)) ρ := by
  obtain ⟨l,r,hl,hr,hle,heq,hgap⟩ := pointwiseAggregate b e ρ
  constructor
  · rintro ⟨l',r',hl',hr',hlt⟩ h
    have hll := ParametricSourceEraser.Proof.scalar_unique _ _ _ _ _ hl' hl
    have hrr := ParametricSourceEraser.Proof.scalar_unique _ _ _ _ _ hr' hr
    have hh := heq.mpr h
    omega
  · intro hn
    have hg := hgap hn
    exact ⟨l,r,hl,hr,by omega⟩
end LogicLineages.OrdinalComparison.Source.SourceMachineAggregateBridge.Proof
