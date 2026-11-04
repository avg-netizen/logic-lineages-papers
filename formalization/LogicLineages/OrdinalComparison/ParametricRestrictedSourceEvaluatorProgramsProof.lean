module
public import LogicLineages.OrdinalComparison.ParametricRestrictedSourceEvaluatorTargets
public import LogicLineages.OrdinalComparison.WWDefaultSourceAssignmentPrimitiveProof
public import LogicLineages.OrdinalComparison.SourceGroundComponentEnvironmentProgramsProof
public import LogicLineages.OrdinalComparison.ParametricOmegaFreeEvaluatorProgramsProof
public import LogicLineages.OrdinalComparison.SourceMachineControlNonperiodicityParityProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricRestrictedSourceEvaluator.Proof
attribute [local irreducible] Computable Partrec Nat.unpair Nat.sqrt

private abbrev Input := (Nat × Nat) × (Nat × List Nat)

private theorem context_primitive :
    Primrec (fun p : Input => List.replicate p.1.2 (SyntaxCode.typeCode Ty.ground)) := by
  have h : Primrec (fun p : Input => (List.range p.1.2).map
      (fun _ => SyntaxCode.typeCode Ty.ground)) :=
    Primrec.list_map (Primrec.list_range.comp (Primrec.snd.comp Primrec.fst))
    (Primrec.const (SyntaxCode.typeCode Ty.ground)).to₂
  apply h.of_eq
  intro p
  simp

private theorem assignment_primitive : Primrec (fun p : Input =>
    DefaultSourceAssignment.assignmentCode
      (List.replicate p.1.2 (SyntaxCode.typeCode Ty.ground)) p.2.1) :=
  DefaultSourceAssignment.Proof.assignmentPrimitiveRecursive.comp
    (context_primitive.pair (Primrec.fst.comp Primrec.snd))

private theorem guard_primitive : PrimrecPred (fun p : Input =>
    p.2.2.length=p.1.2 ∧ SyntaxCode.check
      (List.replicate p.1.2 (SyntaxCode.typeCode Ty.ground)) p.2.1 =
        some (SyntaxCode.typeCode Ty.ground)) := by
  have hlen : Primrec (fun p : Input => p.2.2.length) :=
    Primrec.list_length.comp (Primrec.snd.comp Primrec.snd)
  have hcheck := SyntaxCode.StatementChecks.checkPrimitiveRecursive.comp
    (context_primitive.pair (Primrec.fst.comp Primrec.snd))
  exact (Primrec.eq.comp hlen (Primrec.snd.comp Primrec.fst)).and
    (Primrec.eq.comp hcheck (Primrec.const (some (SyntaxCode.typeCode Ty.ground))))

private theorem scalar_computable (H : Nat × Nat → Nat) (hH : Computable H) :
    Computable (fun p : Input × Nat => ParametricOmegaFreeEvaluator.evaluate H p.1.1.1
      (SourceGroundComponentEnvironment.environment p.1.2.2) p.2) := by
  have hi : Primrec (fun p : Input × Nat => p.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have he : Primrec (fun p : Input × Nat => SourceGroundComponentEnvironment.environment p.1.2.2) :=
    SourceGroundComponentEnvironment.Proof.uniformPrimitiveRecursive.2.2.comp
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  exact (ParametricOmegaFreeEvaluator.Proof.uniformComputable H hH).comp
    ((hi.pair he).pair Primrec.snd).to_comp

private theorem successful_computable (H : Nat × Nat → Nat) (hH : Computable H) :
    Computable (fun p : Input =>
      (DefaultSourceAssignment.assignmentCode
        (List.replicate p.1.2 (SyntaxCode.typeCode Ty.ground)) p.2.1).bind (fun vector =>
          (vector[0]?).bind (fun scalar => some
            (ParametricOmegaFreeEvaluator.evaluate H p.1.1
              (SourceGroundComponentEnvironment.environment p.2.2) scalar)))) := by
  apply Computable.option_bind assignment_primitive.to_comp
  apply Computable.option_bind (Computable.list_getElem?.comp Computable.snd (Computable.const 0))
  exact (Computable.option_some.comp ((scalar_computable H hH).comp
    ((Computable.fst.comp Computable.fst).pair Computable.snd))).to₂

/-- The checked, partial source evaluator is uniformly computable. -/
theorem uniformComputable : Targets.UniformComputable := by
  intro H hH
  simpa only [Bool.cond_decide,evaluate,Bind.bind,Pure.pure,Option.map_eq_bind] using
    Computable.cond guard_primitive.decide.to_comp (successful_computable H hH)
      (Computable.const none)

/-- Each fixed control gamma gives a computable checked source evaluator. -/
theorem fixedGammaComputable : Targets.FixedGammaComputable := by
  intro b
  have hg : Computable (SourceMachineControlNonperiodicity.gamma b) :=
    (SourceMachineControlNonperiodicity.Proof.gamma_primitive b).to_comp
  have h := uniformComputable (fun p : Nat × Nat => SourceMachineControlNonperiodicity.gamma b p.2)
    (hg.comp Computable.snd)
  exact h.comp (((Computable.const 0).pair Computable.fst).pair Computable.snd)
end LogicLineages.OrdinalComparison.Source.ParametricRestrictedSourceEvaluator.Proof
