module
public import LogicLineages.OrdinalComparison.ParametricPairValuePrimitiveTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricPairValuePrimitive.Proof

private theorem rec_eq_iterate (f : Nat → Nat) (seed n : Nat) :
    Nat.rec seed (fun _ r => f r) n=f^[n] seed := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change f (Nat.rec seed (fun _ r => f r) n)=f^[n+1] seed
    rw [Function.iterate_succ_apply',ih]

/-- The explicit indexed iteration formula is primitive recursive without order hypotheses. -/
theorem iterate_primitive (H : Nat × Nat → Nat) (hH : Primrec H) : Primrec (iterateValue H) := by
  have hn : Primrec (fun p : Nat × (Nat × Nat) => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hseed : Primrec (fun p : Nat × (Nat × Nat) => 2*p.2.1+p.2.2) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) hn)
      (Primrec.snd.comp Primrec.snd)
  have hbody : Primrec (fun p : (Nat × (Nat × Nat)) × (Nat × Nat) => H (p.1.1,p.2.2)) :=
    hH.comp ((Primrec.fst.comp Primrec.fst).pair (Primrec.snd.comp Primrec.snd))
  have hit : Primrec (fun p : Nat × (Nat × Nat) =>
      ((fun n => H (p.1,n))^[p.2.1]) (2*p.2.1+p.2.2)) := by
    apply (Primrec.nat_rec' hn hseed hbody.to₂).of_eq
    intro p
    exact rec_eq_iterate (fun n => H (p.1,n)) (2*p.2.1+p.2.2) p.2.1
  exact Primrec.nat_add.comp hit hn
end LogicLineages.OrdinalComparison.Source.ParametricPairValuePrimitive.Proof
