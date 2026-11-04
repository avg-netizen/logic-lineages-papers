module
public import LogicLineages.OrdinalComparison.ParametricOmegaFreeEvaluatorTargets
public import LogicLineages.OrdinalComparison.ParametricPairCollapseComputableProof
public import LogicLineages.OrdinalComparison.OrdinalSyntaxComputableFoldProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricOmegaFreeEvaluator.Proof
attribute [local irreducible] Computable Partrec Nat.unpair Nat.sqrt

private theorem leaf_primitive : Primrec leaf := by
  have hcode : Primrec (fun p : Parameter × Nat => p.2) := Primrec.snd
  have henv : Primrec (fun p : Parameter × Nat => p.1.2) := Primrec.snd.comp Primrec.fst
  have htag := Primrec.nat_mod.comp hcode (Primrec.const 8)
  have hindex := Primrec.nat_div.comp hcode (Primrec.const 8)
  exact Primrec.ite (Primrec.eq.comp hcode (Primrec.const 1)) (Primrec.const 1)
    (Primrec.ite (Primrec.eq.comp htag (Primrec.const 3))
      ((Primrec.list_getD 0).comp henv hindex) (Primrec.const 0))

private theorem computable_ite {P A : Type} [Primcodable P] [Primcodable A]
    {p : P → Prop} [DecidablePred p] {f g : P → A}
    (hp : PrimrecPred p) (hf : Computable f) (hg : Computable g) :
    Computable (fun x => if p x then f x else g x) := by
  simpa only [Bool.cond_decide] using Computable.cond hp.decide.to_comp hf hg

private theorem branch_computable (H : Nat × Nat → Nat) (hH : Computable H) :
    Computable (branch H) := by
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
  have hcollapse : Computable (fun p : X =>
      ParametricPairCollapseComputable.actualValue H (p.1.1,p.2.2.1,p.2.2.2)) :=
    (ParametricPairCollapseComputable.Proof.uniformComputable H hH).comp
      (hindex.pair (hleft.pair hright)).to_comp
  exact computable_ite (Primrec.eq.comp htag (Primrec.const 4)) hadd.to_comp
    (computable_ite (Primrec.eq.comp htag (Primrec.const 5)) hmul.to_comp
      (computable_ite (Primrec.eq.comp htag (Primrec.const 6)) hcollapse (Computable.const 0)))

/-- The raw evaluator is uniformly computable in a first-order indexed budget. -/
theorem uniformComputable : Targets.UniformComputable := by
  intro H hH
  exact OrdinalSyntaxComputableFold.Proof.indexedComputable Parameter Nat leaf (branch H)
    leaf_primitive.to_comp (branch_computable H hH)
end LogicLineages.OrdinalComparison.Source.ParametricOmegaFreeEvaluator.Proof
