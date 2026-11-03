module
public import LogicLineages.OrdinalComparison.FixedSeedControlResidueTargets
public import LogicLineages.OrdinalComparison.ControlComputability
@[expose] public section
namespace LogicLineages.OrdinalComparison.FixedSeedControlResidue.Proof

/-- The iterator has the literal constant initial seed 1, not the input n. -/
theorem H_primitive : Primrec H := by
  have hstep : Primrec₂ (fun (_ : Nat) (x : Nat) => Phi x) :=
    Phi_primrec.comp Primrec.snd
  exact Primrec.nat_iterate Primrec.id (Primrec.const 1) hstep

theorem uniformPrimitiveRecursiveData : Targets.UniformPrimitiveRecursiveData :=
  ⟨H_primitive,
    Primrec.nat_mod.comp (fixed_fastControl_primrec 1) Primrec.id,
    fun m hm => Nat.mod_lt _ hm⟩

end LogicLineages.OrdinalComparison.FixedSeedControlResidue.Proof
