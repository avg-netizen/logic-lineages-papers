module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.SeededSystemCodeTargets
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.SeededSourceCodeProgramsProof
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.SeededInputCodeProgramsProof
public import LogicLineages.OrdinalComparison.SourcePlanPrefixCodeProof
public import LogicLineages.OrdinalComparison.SourceGammaAggregateCodeProgramsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.SeededSystemCode.Proof
open SeededSourceCode (appCode lamCode weakenCode combineCode)
attribute [local irreducible] Nat.sqrt Nat.unpair

private theorem app_pr : Primrec₂ appCode :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 8) Primrec₂.natPair) (Primrec.const 5)
private theorem lam_pr : Primrec₂ lamCode :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 8) Primrec₂.natPair) (Primrec.const 6)
private theorem weaken_pr : Primrec weakenCode :=
  ContextInsertionCode.Proof.primitiveRecursiveAlgorithms.1.comp
    ((Primrec.const 0).pair ((Primrec.const 1).pair Primrec.id))

theorem align_pr : Primrec₂ alignCode :=
  app_pr.comp (lam_pr.comp (Primrec.const 0) (weaken_pr.comp Primrec.fst)) Primrec.snd

theorem payload_pr : Primrec₂ payloadCode := by
  have haa : Primrec (fun p : Nat × Nat => combineCode p.1 p.1) := SeededSourceCode.Proof.combine_pr.comp Primrec.fst Primrec.fst
  have hbb : Primrec (fun p : Nat × Nat => combineCode p.2 p.2) := SeededSourceCode.Proof.combine_pr.comp Primrec.snd Primrec.snd
  have hab : Primrec (fun p : Nat × Nat => combineCode p.1 p.2) := SeededSourceCode.Proof.combine_pr.comp Primrec.fst Primrec.snd
  have hba : Primrec (fun p : Nat × Nat => combineCode p.2 p.1) := SeededSourceCode.Proof.combine_pr.comp Primrec.snd Primrec.fst
  exact app_pr.comp hba (app_pr.comp hab (app_pr.comp hbb (app_pr.comp haa (Primrec.const 1))))

theorem left_pr : Primrec₂ leftCode :=
  SourceGammaAggregateCode.Proof.uniformPrimitiveRecursive.1.comp
    (app_pr.comp (SeededSourceCode.Proof.combine_pr.comp Primrec.fst Primrec.fst) payload_pr)
    (app_pr.comp (SeededSourceCode.Proof.combine_pr.comp Primrec.snd Primrec.snd) payload_pr)

theorem right_pr : Primrec₂ rightCode :=
  SourceGammaAggregateCode.Proof.uniformPrimitiveRecursive.1.comp
    (app_pr.comp (SeededSourceCode.Proof.combine_pr.comp Primrec.fst Primrec.snd) payload_pr)
    (app_pr.comp (SeededSourceCode.Proof.combine_pr.comp Primrec.snd Primrec.fst) payload_pr)

theorem detector_pr : Primrec detectorCode := by
  have hq := SourcePlanPrefixCode.Proof.uniformPrimitiveRecursive.1.comp
    ((Primrec.const 2).pair (Primrec.id (α := Nat × Nat)))
  have ha := align_pr.comp (Primrec.fst.comp hq) (Primrec.const 0)
  have hb := align_pr.comp (Primrec.snd.comp hq) (Primrec.const 8)
  exact (left_pr.comp ha hb).pair (right_pr.comp ha hb)

theorem step_pr : Primrec (fun p : Nat × Nat × State => step p.1 p.2.1 p.2.2) := by
  have hn : Primrec (fun p : Nat × Nat × State => p.1) := Primrec.fst
  have hd : Primrec (fun p : Nat × Nat × State => p.2.1) := Primrec.fst.comp Primrec.snd
  have hk : Primrec (fun p : Nat × Nat × State => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have ht : Primrec (fun p : Nat × Nat × State => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hp := Primrec.fst.comp (SeededSourceCode.Proof.compiler_pr.comp hn
    (SeededInputCode.Proof.subtract_seed_pr.comp hn hd))
  have hdet := detector_pr.comp (SourcePlanPrefixCode.Proof.uniformPrimitiveRecursive.1.comp
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
  ⟨align_pr, payload_pr, left_pr, right_pr, detector_pr, step_pr, system_pr, strict_pr, weak_pr, context_pr⟩

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.SeededSystemCode.Proof
