module
public import LogicLineages.OrdinalComparison.ParametricOmegaFreePrimitiveTargets
public import LogicLineages.OrdinalComparison.ParametricPairValuePrimitiveProof
public import LogicLineages.OrdinalComparison.OrdinalSyntaxPrimitiveFoldProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricOmegaFreePrimitive.Proof
open ParametricOmegaFreeEvaluator
attribute [local irreducible] Nat.unpair Nat.sqrt

private theorem leaf_primitive : Primrec leaf := by
  have hcode : Primrec (fun p : Parameter × Nat => p.2) := Primrec.snd
  have henv : Primrec (fun p : Parameter × Nat => p.1.2) := Primrec.snd.comp Primrec.fst
  have htag := Primrec.nat_mod.comp hcode (Primrec.const 8)
  have hindex := Primrec.nat_div.comp hcode (Primrec.const 8)
  exact Primrec.ite (Primrec.eq.comp hcode (Primrec.const 1)) (Primrec.const 1)
    (Primrec.ite (Primrec.eq.comp htag (Primrec.const 3))
      ((Primrec.list_getD 0).comp henv hindex) (Primrec.const 0))

private theorem branch_primitive (H : Nat × Nat → Nat) (hH : Primrec H)
    (hm : ∀ i : Nat, StrictMono (fun n => H (i,n)))
    (hi : ∀ i n : Nat, n≤H (i,n)) : Primrec (branch H) := by
  let X := Parameter × (Nat × Nat × Nat)
  have htag : Primrec (fun p : X => p.2.1) := Primrec.fst.comp Primrec.snd
  have hleft : Primrec (fun p : X => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hright : Primrec (fun p : X => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hindex : Primrec (fun p : X => p.1.1) := Primrec.fst.comp Primrec.fst
  have hpow : Primrec₂ ((· ^ ·) : Nat → Nat → Nat) :=
    Primrec₂.unpaired'.1 Nat.Primrec.pow
  have hadd := Primrec.nat_add.comp hleft hright
  have hmul := Primrec.nat_mul.comp (hpow.comp (Primrec.const 2) hleft) hright
  have hcollapse : Primrec (fun p : X =>
      ParametricPairCollapseComputable.actualValue H (p.1.1,p.2.2.1,p.2.2.2)) :=
    (ParametricPairValuePrimitive.Proof.uniformPrimitiveRecursive.2 H hH hm hi).comp
      (hindex.pair (hleft.pair hright))
  exact Primrec.ite (Primrec.eq.comp htag (Primrec.const 4)) hadd
    (Primrec.ite (Primrec.eq.comp htag (Primrec.const 5)) hmul
      (Primrec.ite (Primrec.eq.comp htag (Primrec.const 6)) hcollapse (Primrec.const 0)))

/-- The unchanged raw evaluator is primitive recursive for jointly primitive-recursive increasing budgets. -/
theorem uniformPrimitiveRecursive : Targets.UniformPrimitiveRecursive := by
  intro H hH hm hi
  exact OrdinalSyntaxPrimitiveFold.Proof.indexedPrimitiveRecursive Parameter Nat leaf (branch H)
    leaf_primitive (branch_primitive H hH hm hi)

/-- Each fixed gamma specializes the joint primitive-recursive raw evaluator. -/
theorem fixedGammaPrimitive : Targets.FixedGammaPrimitive := by
  intro b
  let H : Nat × Nat → Nat := fun p => SourceMachineControlNonperiodicity.gamma b p.2
  have hH : Primrec H := (SourceMachineControlNonperiodicity.Proof.exactControlParity b).1.comp Primrec.snd
  obtain ⟨hm,hi,_⟩ := ParametricCoefficientOne.Proof.actualGammaCoefficientOne b
  have he := uniformPrimitiveRecursive H hH (fun _ => hm) (fun _ => hi)
  exact he.comp (((Primrec.const 0).pair Primrec.fst).pair Primrec.snd)
end LogicLineages.OrdinalComparison.Source.ParametricOmegaFreePrimitive.Proof
