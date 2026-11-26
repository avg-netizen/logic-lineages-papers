module

public import LogicLineages.PersistentMarking.NumberedWindowFreeAddressProgramTargets
import LogicLineages.PersistentMarking.NumberedWindowFieldProgramChecks
import LogicLineages.PersistentMarking.NumberedWindowMarkRootProgramProof
import LogicLineages.PersistentMarking.NumberedWindowCoverBoundsProgramChecks
import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowFreeAddressProgramChecks
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowFreeAddress NumberedWindowFreeAddressProgramTargets
open NumberedWindowFieldAlgorithm (pack)
open NumberedWindowMarkRootProgramProof (nodePrim)
open NumberedWindowCoverBoundsAlgorithm (bounds)

private theorem packPrim : Primrec pack := by
  obtain ⟨p,h⟩ := NumberedWindowFieldProgramChecks.exact_OrderedFieldPrograms.1
  apply ((Proof.primitiveEvaluation 1 p).comp
    (Primrec.vector_cons.comp Primrec.encode (Primrec.const List.Vector.nil))).of_eq
  exact h

private def readContext (n : Nat) : List Nat :=
  ((Encodable.decode n : Option (List Nat)).getD [])

private theorem readPrim : Primrec readContext :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const [])

private theorem coordPrim :
    Primrec (fun p : List Nat × Nat × Nat => freeAddress p.1 p.2.1 p.2.2) := by
  let Input := List Nat × Nat × Nat
  have context : Primrec (fun p : Input => pack p.1) := packPrim.comp Primrec.fst
  have type : Primrec (fun p : Input => p.2.1) := Primrec.fst.comp Primrec.snd
  have name : Primrec (fun p : Input => p.2.2) := Primrec.snd.comp Primrec.snd
  have term := nodePrim.comp (Primrec.const 0)
    (Primrec.list_cons.comp type (Primrec.list_cons.comp name (Primrec.const [])))
  exact nodePrim.comp (Primrec.const 3) (Primrec.list_cons.comp context
    (Primrec.list_cons.comp type (Primrec.list_cons.comp term (Primrec.const []))))

private theorem namePrim : Primrec freshName := by
  have measurePrim : Primrec bounds := Primrec.encode_iff.mp
    ((Proof.unaryCorrespondence _).mpr NumberedWindowCoverBoundsProgramChecks.exact_MeasureProgram)
  exact Primrec.succ.comp (Primrec.snd.comp (Primrec.fst.comp measurePrim))

theorem exact_FreeAddressPrograms : FreeAddressPrograms := by
  constructor
  · let V := List.Vector Nat 3
    have context : Primrec (fun v : V => readContext v.head) := readPrim.comp Primrec.vector_head
    have tail : Primrec (fun v : V => v.tail) := Primrec.vector_tail
    have type := Primrec.vector_head.comp tail
    have name := Primrec.vector_head.comp (Primrec.vector_tail.comp tail)
    obtain ⟨p,h⟩ := Proof.allPrimitiveFunctions 3 _ (coordPrim.comp (context.pair (type.pair name)))
    refine ⟨p,fun Γ σ v => ?_⟩
    have restored : readContext (Encodable.encode Γ) = Γ := by
      change ((Encodable.decode (Encodable.encode Γ) : Option (List Nat)).getD []) = Γ
      rw [Encodable.encodek]
      rfl
    have eq := h (Encodable.encode Γ ::ᵥ σ ::ᵥ v ::ᵥ nil)
    change evaluate p (Encodable.encode Γ ::ᵥ σ ::ᵥ v ::ᵥ nil) =
      freeAddress (readContext (Encodable.encode Γ)) σ v at eq
    rw [restored] at eq
    exact eq
  · exact (Proof.unaryCorrespondence _).mp namePrim

#print axioms exact_FreeAddressPrograms

end LogicLineages.PersistentMarking.NumberedWindowFreeAddressProgramChecks
