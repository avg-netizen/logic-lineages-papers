module

public import LogicLineages.PersistentMarking.NumberedWindowShiftStepPrograms
import LogicLineages.PersistentMarking.NumberedWindowHeadDeclarationPrograms
import LogicLineages.PersistentMarking.NumberedWindowSyntaxProgramProof
import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowShiftProgramProof
open LogicLineages.ComputabilityKnowledge NumberedWindowShiftAlgorithm List.Vector
open NumberedWindowShiftProgramTargets NumberedWindowShiftStepPrograms
open NumberedWindowHeadDeclarationPrograms (guardOption)

private theorem nextPrim : Primrec (fun p : StepInput => next p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) :=
  termNextPrim.pair (argsNextPrim.comp (Primrec.snd.comp Primrec.snd : Primrec (fun p : StepInput => p.2.2)))

abbrev Parameters := Nat × Nat × Nat
abbrev LayerInput := Parameters × Nat × Table

private theorem layerPrim : Primrec (fun p : LayerInput => layer p.1.1 p.1.2.1 p.1.2.2 p.2.1 p.2.2) := by
  have bound : Primrec (fun p : LayerInput => p.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  let E := LayerInput × Nat
  have amount : Primrec (fun p : E => p.1.1.1) := Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have cutoff : Primrec (fun p : E => p.1.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have rest : Primrec (fun p : E => p.1.2) := Primrec.snd.comp Primrec.fst
  have step := nextPrim.comp (amount.pair (cutoff.pair (Primrec.snd.pair rest)))
  exact Primrec.list_map (Primrec.list_range.comp (Primrec.succ.comp bound)) step.to₂

private theorem tablePrim : Primrec₂ (fun (p : Parameters) n => table p.1 p.2.1 p.2.2 n) := by
  have step : Primrec₂ (fun p (x : Nat × Table) =>
      x.2 ++ [layer p.1 p.2.1 p.2.2 x.1 x.2]) :=
    Primrec.list_append.comp (Primrec.snd.comp Primrec.snd)
      (Primrec.list_cons.comp layerPrim (Primrec.const []))
  apply (Primrec.nat_rec (Primrec.const ([] : Table)) step).of_eq
  intro p n
  induction n with
  | zero => rfl
  | succ n ih =>
    change _ ++ [_] = _
    simp only [table,← ih]

private theorem computedPrim :
    Primrec (fun p : Nat × Nat × Nat × Nat × Nat => computed p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  let P := Nat × Nat × Nat × Nat × Nat
  have amount : Primrec (fun p : P => p.1) := Primrec.fst
  have cutoff : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
  have bound : Primrec (fun p : P => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have code : Primrec (fun p : P => p.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have offset : Primrec (fun p : P => p.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have tab := tablePrim.comp (amount.pair (cutoff.pair bound)) code
  exact nextPrim.comp (amount.pair (cutoff.pair (offset.pair (code.pair tab))))

theorem outputPrim : Primrec (fun p : Nat × Nat × Nat => output p.1 p.2.1 p.2.2) := by
  let P := Nat × Nat × Nat
  have amount : Primrec (fun p : P => p.1) := Primrec.fst
  have cutoff : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
  have code : Primrec (fun p : P => p.2.2) := Primrec.snd.comp Primrec.snd
  have valid := NumberedWindowSyntaxProgramProof.bits.comp code
  have row := computedPrim.comp (amount.pair (cutoff.pair (code.pair (code.pair (Primrec.const 0)))))
  exact (guardOption (Primrec.fst.comp valid) (Primrec.fst.comp row)).pair
    (guardOption (Primrec.snd.comp valid) (Primrec.snd.comp row))

theorem program : ShiftProgram := by
  have amount : Primrec (fun v : List.Vector Nat 3 => v.head) := Primrec.vector_head
  have cutoff := Primrec.vector_head.comp
    (Primrec.vector_tail : Primrec (fun v : List.Vector Nat 3 => v.tail))
  have code := Primrec.vector_head.comp (Primrec.vector_tail.comp
    (Primrec.vector_tail : Primrec (fun v : List.Vector Nat 3 => v.tail)))
  obtain ⟨p,h⟩ := GorbowPRProgram.Proof.allPrimitiveFunctions 3 _
    (Primrec.encode.comp (outputPrim.comp (amount.pair (cutoff.pair code))))
  exact ⟨p,fun a c n => h (a ::ᵥ c ::ᵥ n ::ᵥ List.Vector.nil)⟩

end LogicLineages.PersistentMarking.NumberedWindowShiftProgramProof
