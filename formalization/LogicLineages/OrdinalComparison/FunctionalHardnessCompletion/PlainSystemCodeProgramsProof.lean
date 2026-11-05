module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.PlainSystemCodeTargets
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.SeededSystemCodeProgramsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.PlainSystemCode.Proof
open SeededSourceCode (appCode lamCode)
attribute [local irreducible] Nat.sqrt Nat.unpair

private theorem app_pr : Primrec₂ appCode :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 8) Primrec₂.natPair) (Primrec.const 5)

theorem step_pr : Primrec (fun p : Nat × Nat × State => step p.1 p.2.1 p.2.2) := by
  have hn : Primrec (fun p : Nat × Nat × State => p.1) := Primrec.fst
  have hd : Primrec (fun p : Nat × Nat × State => p.2.1) := Primrec.fst.comp Primrec.snd
  have hk : Primrec (fun p : Nat × Nat × State => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have ht : Primrec (fun p : Nat × Nat × State => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hp := Primrec.fst.comp (SeededSourceCode.Proof.compiler_pr.comp hn
    hd)
  have hdet := SeededSystemCode.Proof.detector_pr.comp (SourcePlanPrefixCode.Proof.uniformPrimitiveRecursive.1.comp
    (hk.pair hp))
  have htail := SourcePlanPrefixCode.Proof.uniformPrimitiveRecursive.2.comp (Primrec.const 2) ht
  exact (Primrec.nat_add.comp hk (Primrec.const 2)).pair (Primrec.list_cons.comp hdet htail)

theorem system_pr : Primrec₂ systemCode :=
  Primrec.list_foldr Primrec.snd (Primrec.const (0, []))
    (step_pr.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)).to₂

theorem strict_pr : Primrec₂ strictCode :=
  SourceGammaAggregateCode.Proof.uniformPrimitiveRecursive.2.2.2.2.comp (Primrec.snd.comp system_pr)

theorem weak_pr : Primrec₂ weakCode :=
  (app_pr.comp (Primrec.const (lamCode 0 1)) (Primrec.snd.comp strict_pr)).pair
    (app_pr.comp (Primrec.const (lamCode 0 0)) (Primrec.fst.comp strict_pr))

private theorem replicate_pr : Primrec₂ (fun n a : Nat => List.replicate n a) := by
  apply (Primrec.nat_iterate Primrec.fst (Primrec.const ([] : List Nat))
    (Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂).of_eq
  intro p
  induction p.1 with
  | zero => rfl
  | succ n ih =>
      change (fun b : List Nat => p.2 :: b)^[n+1] [] = List.replicate (n+1) p.2
      rw [Function.iterate_succ_apply', List.replicate_succ]
      exact congrArg (List.cons p.2) ih

theorem context_pr : Primrec₂ contextCode :=
  Primrec.list_append.comp
    (replicate_pr.comp (Primrec.fst.comp system_pr) (Primrec.const 0))
    (replicate_pr.comp Primrec.fst (Primrec.const (SyntaxCode.typeCode FunctionalDetector.unary)))

theorem numericalPrograms : Targets.NumericalPrograms :=
  ⟨step_pr, system_pr, strict_pr, weak_pr, context_pr⟩

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.PlainSystemCode.Proof
