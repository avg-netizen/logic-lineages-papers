module
public import LogicLineages.OrdinalComparison.ControlTargets
public import LogicLineages.OrdinalComparison.ComputabilityTargets
public import Mathlib.Computability.Partrec

@[expose] public section

/-! Independent full statement of paper 05, foundations.tex,
`lem:phi-growth` (Elementary control properties). This file imports the literal
definitions and standard predicates only, and no new control proofs. -/

namespace LogicLineages.OrdinalComparison.Targets

def ElementaryControlProperties : Prop :=
  Computable Phi ∧ StrictMono Phi ∧ ∀ n : Nat,
    n < Phi n ∧ 2 ^ (2 ^ Phi n) ≤ Phi (n + 1) ∧
      4 * Phi n + 4 < Phi (n + 1)

end LogicLineages.OrdinalComparison.Targets
