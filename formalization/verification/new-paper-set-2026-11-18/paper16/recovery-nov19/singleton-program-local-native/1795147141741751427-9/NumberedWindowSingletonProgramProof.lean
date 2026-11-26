module

public import LogicLineages.PersistentMarking.NumberedWindowSingletonStepPrograms
import LogicLineages.PersistentMarking.NumberedWindowHeadDeclarationPrograms
import LogicLineages.PersistentMarking.NumberedWindowSyntaxProgramProof
import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowSingletonProgramProof
open LogicLineages.ComputabilityKnowledge NumberedWindowSingletonAlgorithm List.Vector
open NumberedWindowShiftAlgorithm (Table)
open NumberedWindowShiftStepPrograms (StepInput)
open NumberedWindowSingletonProgramTargets NumberedWindowSingletonStepPrograms
open NumberedWindowHeadDeclarationPrograms (guardOption)

abbrev Parameters := Nat × Nat × Nat
abbrev LayerInput := Parameters × Nat × Table

private theorem layerPrim : Primrec (fun p : LayerInput => (List.range (p.1.2.2+1)).map (fun offset => next p.1.1 p.1.2.1 offset p.2.1 p.2.2)) := by
  have bound : Primrec (fun p : LayerInput => p.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  let E := LayerInput × Nat
  have inserted : Primrec (fun p : E => p.1.1.1) := Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have depth : Primrec (fun p : E => p.1.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have rest : Primrec (fun p : E => p.1.2) := Primrec.snd.comp Primrec.fst
  have step := nextPrim.comp (inserted.pair (depth.pair (Primrec.snd.pair rest)))
  exact Primrec.list_map (Primrec.list_range.comp (Primrec.succ.comp bound)) step.to₂

private theorem tablePrim : Primrec₂ (fun (p : Parameters) n => table p.1 p.2.1 p.2.2 n) := by
  have step : Primrec₂ (fun (p : Parameters) (x : Nat × Table) =>
      x.2 ++ [(List.range (p.2.2+1)).map (fun offset => next p.1 p.2.1 offset x.1 x.2)]) :=
    Primrec.list_append.comp (Primrec.snd.comp Primrec.snd)
      (Primrec.list_cons.comp layerPrim (Primrec.const []))
  apply (Primrec.nat_rec (Primrec.const ([] : Table)) step).of_eq
  intro p n
  induction n with
  | zero => rfl
  | succ n ih =>
    change _ ++ [_] = _
    simp only [table,← ih]

private def topInput (p : Parameters) : StepInput :=
  (p.1,p.2.1,0,p.2.2,table p.1 p.2.1 p.2.2 p.2.2)

-- Bound the elaboration effort for specializing the nested matrix's inputs.
set_option maxHeartbeats 600000 in
private theorem topInputPrim : Primrec topInput := by
  have inserted : Primrec (fun p : Parameters => p.1) := Primrec.fst
  have depth : Primrec (fun p : Parameters => p.2.1) := Primrec.fst.comp Primrec.snd
  have code : Primrec (fun p : Parameters => p.2.2) := Primrec.snd.comp Primrec.snd
  have tab : Primrec (fun p : Parameters => table p.1 p.2.1 p.2.2 p.2.2) :=
    tablePrim.comp Primrec.id code
  have input : Primrec (fun p : Parameters =>
      ((p.1,p.2.1,0,p.2.2,table p.1 p.2.1 p.2.2 p.2.2) : StepInput)) :=
    inserted.pair (depth.pair ((Primrec.const 0).pair (code.pair tab)))
  exact input

private theorem topRowPrim :
    Primrec (fun p : Parameters => computed p.1 p.2.1 p.2.2 p.2.2 0) :=
  (nextPrim.comp topInputPrim).of_eq (fun _ => rfl)

theorem outputPrim : Primrec (fun p : Nat × Nat × Nat => output p.1 p.2.1 p.2.2) := by
  let P := Nat × Nat × Nat
  have inserted : Primrec (fun p : P => p.1) := Primrec.fst
  have depth : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
  have code : Primrec (fun p : P => p.2.2) := Primrec.snd.comp Primrec.snd
  have valid := NumberedWindowSyntaxProgramProof.bits.comp code
  have arg := Primrec.fst.comp (NumberedWindowSyntaxProgramProof.bits.comp inserted)
  exact (guardOption (Primrec.and.comp arg (Primrec.fst.comp valid)) (Primrec.fst.comp topRowPrim)).pair
    (guardOption (Primrec.and.comp arg (Primrec.snd.comp valid)) (Primrec.snd.comp topRowPrim))

theorem program : SingletonProgram := by
  have inserted : Primrec (fun v : List.Vector Nat 3 => v.head) := Primrec.vector_head
  have depth := Primrec.vector_head.comp
    (Primrec.vector_tail : Primrec (fun v : List.Vector Nat 3 => v.tail))
  have code := Primrec.vector_head.comp (Primrec.vector_tail.comp
    (Primrec.vector_tail : Primrec (fun v : List.Vector Nat 3 => v.tail)))
  obtain ⟨p,h⟩ := GorbowPRProgram.Proof.allPrimitiveFunctions 3 _
    (Primrec.encode.comp (outputPrim.comp (inserted.pair (depth.pair code))))
  exact ⟨p,fun a c n => h (a ::ᵥ c ::ᵥ n ::ᵥ List.Vector.nil)⟩

end LogicLineages.PersistentMarking.NumberedWindowSingletonProgramProof
