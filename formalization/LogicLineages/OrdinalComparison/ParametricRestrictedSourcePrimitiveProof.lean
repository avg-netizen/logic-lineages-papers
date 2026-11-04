module
public import LogicLineages.OrdinalComparison.ParametricRestrictedSourcePrimitiveTargets
public import LogicLineages.OrdinalComparison.WWDefaultSourceAssignmentPrimitiveProof
public import LogicLineages.OrdinalComparison.SourceGroundComponentEnvironmentProgramsProof
public import LogicLineages.OrdinalComparison.ParametricOmegaFreePrimitiveProof
public import LogicLineages.OrdinalComparison.SourceMachineControlNonperiodicityParityProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricRestrictedSourcePrimitive.Proof
open ParametricRestrictedSourceEvaluator
attribute [local irreducible] Nat.unpair Nat.sqrt

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

private theorem scalar_primitive (H : Nat × Nat → Nat) (hH : Primrec H)
    (hm : ∀ i : Nat, StrictMono (fun n => H (i,n)))
    (hmajor : ∀ i n : Nat, n≤H (i,n)) :
    Primrec (fun p : Input × Nat => ParametricOmegaFreeEvaluator.evaluate H p.1.1.1
      (SourceGroundComponentEnvironment.environment p.1.2.2) p.2) := by
  have hi : Primrec (fun p : Input × Nat => p.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have he : Primrec (fun p : Input × Nat => SourceGroundComponentEnvironment.environment p.1.2.2) :=
    SourceGroundComponentEnvironment.Proof.uniformPrimitiveRecursive.2.2.comp
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  exact (ParametricOmegaFreePrimitive.Proof.uniformPrimitiveRecursive H hH hm hmajor).comp
    ((hi.pair he).pair Primrec.snd)

private theorem successful_primitive (H : Nat × Nat → Nat) (hH : Primrec H)
    (hm : ∀ i : Nat, StrictMono (fun n => H (i,n)))
    (hmajor : ∀ i n : Nat, n≤H (i,n)) :
    Primrec (fun p : Input =>
      (DefaultSourceAssignment.assignmentCode
        (List.replicate p.1.2 (SyntaxCode.typeCode Ty.ground)) p.2.1).bind (fun vector =>
          (vector[0]?).bind (fun scalar => some
            (ParametricOmegaFreeEvaluator.evaluate H p.1.1
              (SourceGroundComponentEnvironment.environment p.2.2) scalar)))) := by
  apply Primrec.option_bind assignment_primitive
  apply Primrec.option_bind (Primrec.list_getElem?.comp Primrec.snd (Primrec.const 0))
  exact (Primrec.option_some.comp ((scalar_primitive H hH hm hmajor).comp
    ((Primrec.fst.comp Primrec.fst).pair Primrec.snd))).to₂

/-- The unchanged checked Option evaluator is primitive recursive under the indexed budget hypotheses. -/
theorem uniformPrimitiveRecursive : Targets.UniformPrimitiveRecursive := by
  intro H hH hm hmajor
  simpa only [evaluate,Bind.bind,Pure.pure,Option.map_eq_bind] using
    Primrec.ite guard_primitive (successful_primitive H hH hm hmajor) (Primrec.const none)

/-- Each fixed actual gamma yields a primitive-recursive checked source evaluator. -/
theorem fixedGammaPrimitive : Targets.FixedGammaPrimitive := by
  intro b
  let H : Nat × Nat → Nat := fun p => SourceMachineControlNonperiodicity.gamma b p.2
  have hH : Primrec H := (SourceMachineControlNonperiodicity.Proof.exactControlParity b).1.comp Primrec.snd
  obtain ⟨hm,hi,_⟩ := ParametricCoefficientOne.Proof.actualGammaCoefficientOne b
  have he := uniformPrimitiveRecursive H hH (fun _ => hm) (fun _ => hi)
  exact he.comp (((Primrec.const 0).pair Primrec.fst).pair Primrec.snd)
end LogicLineages.OrdinalComparison.Source.ParametricRestrictedSourcePrimitive.Proof
