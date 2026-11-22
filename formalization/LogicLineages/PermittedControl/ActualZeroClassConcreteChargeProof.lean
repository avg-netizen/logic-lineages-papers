module
public import LogicLineages.PermittedControl.ActualZeroClassConcreteChargeTargets
import LogicLineages.PermittedControl.ActualZeroClassConcreteAssemblyProof
import LogicLineages.PermittedControl.InnerTerminationProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualZeroClassConcreteCharge
open scoped Classical
open OrdinalComparison ActualRankedRowColumns ActualZeroClassConcreteAssembly

theorem exactConcreteZeroClassCharge : ExactConcreteZeroClassCharge := by
  intro f B hf ρ ordered C r constant raw xs annotations paid bounded normalized aligned ready actualC zero
  dsimp only
  intro tails
  obtain ⟨moved, ledger, x₀, q, hm, hreads, hAnchor, hledger, equations, hrep⟩ :=
    exactConcreteZeroClassAssembly f B hf ρ ordered C r constant raw xs annotations
      paid bounded normalized aligned ready actualC zero tails
  exact ⟨moved, ledger, x₀, q, hm, hreads, hAnchor, hledger, equations, hrep,
    InnerTerminationProof.fullInnerTermination (ValueKey r) (NONote × NONote) r
      (rankedRow r constant raw) (concreteRow f C r constant xs annotations moved) hrep⟩

end LogicLineages.PermittedControl.ActualZeroClassConcreteCharge
