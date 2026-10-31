module
public import LogicLineages.OrdinalComparison.SourcePerturbedControlValuationProof
public import LogicLineages.OrdinalComparison.ControlComputability
@[expose] public section
namespace LogicLineages.OrdinalComparison.PerturbedControl.Proof

theorem error_primitive (b : Nat) (H : Nat×Nat → Bool) (hH : Primrec H) :
    Primrec (error b H) := by
  have hh : Primrec (fun n => H (valuationTwo n,n)) :=
    hH.comp (valuation_primitive.pair Primrec.id)
  have hbit : Primrec (fun n => if H (valuationTwo n,n) then (1:Nat) else 0) :=
    Primrec.ite (Primrec.eq.comp hh (Primrec.const true)) (Primrec.const 1) (Primrec.const 0)
  exact Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 0)) (Primrec.const 0)
    (Primrec.ite (Primrec.nat_le.comp Primrec.id (Primrec.const b)) (Primrec.const 0) hbit)

theorem control_primitive (b : Nat) (H : Nat×Nat → Bool) (hH : Primrec H) :
    Primrec (control b H) :=
  Primrec.nat_add.comp Phi_primrec (error_primitive b H hH)
end LogicLineages.OrdinalComparison.PerturbedControl.Proof
