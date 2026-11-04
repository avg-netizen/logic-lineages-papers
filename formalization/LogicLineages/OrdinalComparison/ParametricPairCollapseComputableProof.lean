module
public import LogicLineages.OrdinalComparison.ParametricPairCollapseComputableSearchProof
public import LogicLineages.OrdinalComparison.SourceMachineControlNonperiodicityParityProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricPairCollapseComputable.Proof
attribute [local irreducible] Computable Partrec Nat.unpair Nat.sqrt

theorem uniformComputable : Targets.UniformComputable := by
  intro H hH
  exact (uniformPartialRecursive H hH).of_eq_tot (fun p => (exactSearch H p).1)

theorem fixedGammaComputable : Targets.FixedGammaComputable := by
  intro b
  have hg : Computable (SourceMachineControlNonperiodicity.gamma b) :=
    (SourceMachineControlNonperiodicity.Proof.exactControlParity b).1.to_comp
  have h := uniformComputable (fun p : Nat × Nat => SourceMachineControlNonperiodicity.gamma b p.2)
    (hg.comp Computable.snd)
  exact (h.comp ((Computable.const 0).pair Computable.id)).of_eq (fun _ => rfl)
end LogicLineages.OrdinalComparison.Source.ParametricPairCollapseComputable.Proof
