module
public import LogicLineages.PersistentMarking.NumberedWindowInternalBetaSubDefinitions
import LogicLineages.PersistentMarking.NumberedWindowSingletonProgramProof
import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalBetaSubSelectionProof

open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowInternalBetaSub

theorem selected : ∃ sub : Program 2, Fits sub := by
  let P := List.Vector Nat 2
  have arg : Primrec (fun v : P => v.head) := Primrec.vector_head
  have body : Primrec (fun v : P => v.tail.head) :=
    Primrec.vector_head.comp Primrec.vector_tail
  have opt := Primrec.fst.comp (NumberedWindowSingletonProgramProof.outputPrim.comp
    (arg.pair ((Primrec.const (0 : Nat)).pair body)))
  have direct : Primrec (fun v : P => code v.head v.tail.head) :=
    Primrec.option_getD.comp ((Primrec.option_map₁ Primrec.succ).comp opt) (Primrec.const 0)
  obtain ⟨p,hp⟩ := Proof.allPrimitiveFunctions 2 _ direct
  exact ⟨p,fun a b => hp (a ::ᵥ b ::ᵥ nil)⟩

#print axioms selected
end LogicLineages.PersistentMarking.NumberedWindowInternalBetaSubSelectionProof
