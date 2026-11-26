module

public import LogicLineages.PersistentMarking.NumberedWindowRawApplicationLiftProgramTargets
import LogicLineages.PersistentMarking.NumberedWindowMarkRootProgramProof
import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowRawApplicationLiftProgramChecks
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowRawApplicationLift NumberedWindowRawApplicationLiftProgramTargets
open NumberedWindowMarkRootProgramProof (nodePrim)

theorem exact_RawApplicationLiftProgram : RawApplicationLiftProgram := by
  let V := List.Vector Nat 6
  have a : Primrec (fun v : V => v.head) := Primrec.vector_head
  have ta : Primrec (fun v : V => v.tail) := Primrec.vector_tail
  have b := Primrec.vector_head.comp ta
  have tb := Primrec.vector_tail.comp ta
  have u := Primrec.vector_head.comp tb
  have tu := Primrec.vector_tail.comp tb
  have q := Primrec.vector_head.comp tu
  have tq := Primrec.vector_tail.comp tu
  have w := Primrec.vector_head.comp tq
  have tw := Primrec.vector_tail.comp tq
  have r := Primrec.vector_head.comp tw
  have node {f : V → Nat} (hf : Primrec f) :
      Primrec (fun v : V => NumberedWindowFieldAlgorithm.packNode 6
        [v.head,v.tail.head,f v,v.tail.tail.head]) :=
    nodePrim.comp (Primrec.const 6) (Primrec.list_cons.comp a (Primrec.list_cons.comp b
      (Primrec.list_cons.comp hf (Primrec.list_cons.comp u (Primrec.const [])))))
  have witness := nodePrim.comp (Primrec.const 5)
    (Primrec.list_cons.comp w (Primrec.const []))
  have liftPrim : Primrec (fun v : V =>
      lift v.head v.tail.head v.tail.tail.head v.tail.tail.tail.head
        v.tail.tail.tail.tail.head v.tail.tail.tail.tail.tail.head) :=
    (node q).pair (witness.pair (node r))
  obtain ⟨p,h⟩ := Proof.allPrimitiveFunctions 6 _ (Primrec.encode.comp liftPrim)
  exact ⟨p,fun a b u q w r => h (a ::ᵥ b ::ᵥ u ::ᵥ q ::ᵥ w ::ᵥ r ::ᵥ nil)⟩

#print axioms exact_RawApplicationLiftProgram

end LogicLineages.PersistentMarking.NumberedWindowRawApplicationLiftProgramChecks
