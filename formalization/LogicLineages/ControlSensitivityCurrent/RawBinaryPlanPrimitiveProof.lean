module
public import LogicLineages.ControlSensitivityCurrent.RawBinaryPlanStepPrimitiveProof
public import LogicLineages.ControlSensitivityCurrent.BinaryGeneratorProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG.BinaryPlanCompiler

open LogicLineages.OrdinalComparison.Source.SourceBinaryHalvingTrace (TraceState trace)
open PlanCompiler (Instruction)

theorem binders_primitive : Primrec (fun n => List.replicate n binder) := by
  have hcons : Primrec₂ (fun (_ : Nat) (xs : List Instruction) => binder :: xs) :=
    (Primrec.list_cons.comp (Primrec.const binder) Primrec.snd).to₂
  apply (Primrec.nat_iterate Primrec.id (Primrec.const ([] : List Instruction)) hcons).of_eq
  intro n
  simp only [id_eq]
  induction n with
  | zero => rfl
  | succ n ih => simp [Function.iterate_succ_apply', List.replicate_succ, ih]

theorem finish_primitive :
    Primrec (fun p : Nat × BinaryState => finish p.1 p.2) := by
  let A := Nat × BinaryState
  have hout : Primrec (fun p : A => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have htail : Primrec (fun p : A => p.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hn : Primrec (fun p : A => p.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have terminal (tag : Nat) : Primrec (fun p : A => gate (tag,p.2.2.1,0,0,0)) :=
    gate_primitive.comp ((Primrec.const tag).pair (hout.pair (Primrec.const (0,0,0))))
  have hgate := Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0)) (terminal 0) (terminal 3)
  exact Primrec.list_append.comp (binders_primitive.comp hn) (Primrec.list_cons.comp hgate htail)

theorem lower_trace_primitive :
    Primrec (fun p : TraceState × BinaryState => lowerTrace p.1 p.2) := by
  let A := TraceState × BinaryState
  let B := A × (BinaryState × Nat)
  have hbits : Primrec (fun p : A => p.1.2) := Primrec.snd.comp Primrec.fst
  have hstep := binary_step_primitive.comp (Primrec.snd : Primrec (fun p : B => p.2))
  exact finish_primitive.comp ((Primrec.fst.comp Primrec.fst).pair
    (Primrec.list_foldl (Primrec.list_reverse.comp hbits) Primrec.snd hstep.to₂))

theorem primitive : RawBinaryPlanTargets.Primitive := by
  let A := List Nat × Nat × List Instruction
  have hcontext : Primrec (fun p : A => 0 :: p.1) :=
    Primrec.list_cons.comp (Primrec.const 0) Primrec.fst
  have htrace : Primrec trace := BinaryGenerator.uniformPrimitiveRecursive.2
  exact lower_trace_primitive.comp ((htrace.comp (Primrec.fst.comp Primrec.snd)).pair
    (hcontext.pair ((Primrec.const 1).pair ((Primrec.snd.comp Primrec.snd).pair (Primrec.const 1)))))

end LogicLineages.ControlSensitivityCurrent.RawSourceDAG.BinaryPlanCompiler
