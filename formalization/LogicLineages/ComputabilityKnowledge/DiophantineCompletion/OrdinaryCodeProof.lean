module
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.OrdinaryCodeTargets
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.MinimizationDiophantineProof
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.PrimitiveRecursionDiophantineProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.DiophantineCompletion.OrdinaryCodeProof
open Dioph OrdinaryCodeTargets RowPackingClosureProof

/-- Structural induction covers all eight constructors of the actual code
syntax. The partial-recursion and minimization clauses are proved suppliers. -/
theorem fullCodeGraphDiophantine : FullCodeGraphDiophantine := by
  intro c
  induction c with
  | zero => exact Proof.recursionFreeGraphDiophantine .zero .zero
  | succ => exact Proof.recursionFreeGraphDiophantine .succ .succ
  | left => exact Proof.recursionFreeGraphDiophantine .left .left
  | right => exact Proof.recursionFreeGraphDiophantine .right .right
  | pair cf cg ihf ihg =>
      apply (Proof.partialPairClosure _ _ ihf ihg).ext
      intro v
      simp [graph,partialPair,Nat.Partrec.Code.eval,Seq.seq,
        Part.mem_bind_iff,Part.mem_map_iff]
  | comp cf cg ihf ihg =>
      exact Proof.partialCompositionClosure _ _ ihf ihg
  | prec cf cg ihf ihg =>
      exact PrimitiveRecursionDiophantineProof.ordinaryPrecGraphClosure cf cg ihf ihg
  | rfind' cf ih =>
      exact MinimizationDiophantineProof.ordinaryRfindGraphClosure cf ih

theorem partrecGraphDiophantine : PartrecGraphDiophantine := by
  intro f hf
  obtain ⟨c,hc⟩ := Nat.Partrec.Code.exists_code.1 hf
  simpa only [hc] using fullCodeGraphDiophantine c

/-- Use the existing proved partial recursiveness of evaluation to obtain
one fixed ordinary code. This statement is equality of Part values, not just
agreement on terminating cases. -/
theorem fixedUniversalCode : FixedUniversalCode := by
  have hDecode : Computable Nat.Partrec.Code.ofNatCode := by
    simpa only [Nat.Partrec.Code.ofNatCode_eq] using (Computable.ofNat Nat.Partrec.Code)
  have hEval : Partrec₂ (fun e x : Nat =>
      Nat.Partrec.Code.eval (Nat.Partrec.Code.ofNatCode e) x) :=
    (Nat.Partrec.Code.eval_part.comp (hDecode.comp Computable.fst) Computable.snd).to₂
  obtain ⟨u,hu⟩ := Nat.Partrec.Code.exists_code.1 (Partrec₂.unpaired'.2 hEval)
  refine ⟨u,?_⟩
  intro e x
  rw [hu]
  simp only [Nat.unpaired,Nat.unpair_pair]

/-- The unchanged original universal-evaluator comparator. No extraction of
a polynomial from an arbitrary Diophantine proof is asserted. -/
theorem universalEvaluatorDiophantine : Targets.UniversalEvaluatorDiophantine := by
  obtain ⟨u,hu⟩ := fixedUniversalCode
  have h := finCompose (fullCodeGraphDiophantine u)
    ![(fun v : Fin 3 → Nat => Nat.pair (v 0) (v 1)),(fun v => v 2)] (by
      intro i
      fin_cases i
      · exact Proof.pairDiophantine _ _ _ (Dioph.proj_dioph 0) (Dioph.proj_dioph 1)
      · exact Dioph.proj_dioph 2)
  apply h.ext
  intro v
  change v 2 ∈ Nat.Partrec.Code.eval u (Nat.pair (v 0) (v 1)) ↔
    v 2 ∈ Nat.Partrec.Code.eval (Nat.Partrec.Code.ofNatCode (v 0)) (v 1)
  rw [hu]

end LogicLineages.ComputabilityKnowledge.DiophantineCompletion.OrdinaryCodeProof
