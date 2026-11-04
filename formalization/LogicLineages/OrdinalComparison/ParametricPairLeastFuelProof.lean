module
public import LogicLineages.OrdinalComparison.ParametricPairLeastFuelSearchProof
public import LogicLineages.OrdinalComparison.SourceMachineControlNonperiodicityParityProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricPairLeastFuel.Proof
attribute [local irreducible] Computable Partrec Nat.unpair Nat.sqrt

theorem fixedGammaFuel : Targets.FixedGammaFuel := by
  intro b
  have hg : Computable (gammaControl b) :=
    (SourceMachineControlNonperiodicity.Proof.exactControlParity b).1.to_comp.comp Computable.snd
  have hf : Computable (gammaFuel b) :=
    (uniformComputable (gammaControl b) hg).comp ((Computable.const 0).pair Computable.id)
  refine ⟨hf,?_⟩
  intro p
  have h := exactLeastFuel (gammaControl b) (0,p)
  have hc := (ParametricPairMachineCode.Proof.exactCalibration (gammaControl b)).2.2.2
  constructor
  · rw [hc] at h
    exact h.1
  · intro k hk
    have he := h.2.1 k hk
    rw [hc] at he
    exact he
end LogicLineages.OrdinalComparison.Source.ParametricPairLeastFuel.Proof
