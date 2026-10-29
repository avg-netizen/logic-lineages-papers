module
public import LogicLineages.OrdinalComparison.ComputabilityTargets
public import Mathlib.Computability.Partrec

@[expose] public section

/-! The literal control has an encoded primitive-recursive certificate at each
fixed finite hierarchy level. No effective-enumeration oracle is assumed. -/

namespace LogicLineages.OrdinalComparison

theorem fixed_fastControl_primrec (j : Nat) : Primrec (fastControl j) := by
  induction j with
  | zero =>
      have hp : Primrec₂ ((· ^ ·) : Nat → Nat → Nat) :=
        Primrec₂.unpaired'.1 Nat.Primrec.pow
      exact hp.comp (Primrec.const 2) Primrec.id
  | succ j ih =>
      have hstep : Primrec₂ (fun (_ : Nat) (x : Nat) => fastControl j x) :=
        ih.comp Primrec.snd
      exact Primrec.nat_iterate Primrec.succ Primrec.id hstep

theorem Phi_primrec : Primrec Phi :=
  (fixed_fastControl_primrec 5).comp
    (Primrec.nat_add.comp Primrec.id (Primrec.const 100))

theorem Phi_computable : Computable Phi := Phi_primrec.to_comp

theorem fixedControlPrimitiveRecursive : Targets.FixedControlPrimitiveRecursive :=
  ⟨fixed_fastControl_primrec, Phi_primrec⟩

#print axioms fixedControlPrimitiveRecursive

end LogicLineages.OrdinalComparison
