module

public import LogicLineages.PersistentMarking.NumberedWindowDirectClassAddressProgramTargets
import LogicLineages.PersistentMarking.NumberedWindowConcreteCheckersProgramChecks
import LogicLineages.PersistentMarking.NumberedWindowFieldProgramChecks
import LogicLineages.PersistentMarking.NumberedWindowAddressProgramProof
import LogicLineages.PersistentMarking.NumberedWindowMarkRootProgramProof
import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowDirectClassAddressProgramChecks
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowDirectClassAddress NumberedWindowDirectClassAddressProgramTargets
open NumberedWindowAddressAlgorithm (Address addressView)
open NumberedWindowAddressProgramProof (addressPrim)
open NumberedWindowFieldAlgorithm (pack)
open NumberedWindowMarkRootProgramProof (nodePrim)
open NumberedWindowConcreteCheckersProgramChecks (exact_AllFourProgramWitnesses)

private theorem packPrim : Primrec pack := by
  obtain ⟨p,h⟩ := NumberedWindowFieldProgramChecks.exact_OrderedFieldPrograms.1
  apply ((Proof.primitiveEvaluation 1 p).comp
    (Primrec.vector_cons.comp Primrec.encode (Primrec.const List.Vector.nil))).of_eq
  exact h

private theorem singletonPrim : Primrec₂ singleHop := by
  have fields : Primrec (fun p : Nat × Nat => [p.1,p.2]) :=
    Primrec.list_cons.comp Primrec.fst (Primrec.list_cons.comp Primrec.snd (Primrec.const []))
  have node := nodePrim.comp (Primrec.const 2) fields
  exact (packPrim.comp (Primrec.list_cons.comp node (Primrec.const []))).to₂

theorem exact_DirectClassAddressProgram : DirectClassAddressProgram := by
  intro positive h
  obtain ⟨p,hp⟩ := h
  let Input := Nat × Nat × Nat
  have source : Primrec (fun a : Input => a.1) := Primrec.fst
  have cert : Primrec (fun a : Input => a.2.1) := Primrec.fst.comp Primrec.snd
  have target : Primrec (fun a : Input => a.2.2) := Primrec.snd.comp Primrec.snd
  have coordinates := Primrec.vector_cons.comp source (Primrec.vector_cons.comp cert
    (Primrec.vector_cons.comp target (Primrec.const List.Vector.nil)))
  have positivePrim : Primrec (fun a : Input => (positive a.1 a.2.1 a.2.2).toNat) :=
    ((Proof.primitiveEvaluation 3 p).comp coordinates).of_eq
      (fun a => hp a.1 a.2.1 a.2.2)
  let Parsed := Input × Address
  have parsedTarget : Primrec (fun a : Parsed => a.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have wrap := singletonPrim.comp parsedTarget (cert.comp Primrec.fst)
  have evaluated := positivePrim.comp ((source.comp Primrec.fst).pair (wrap.pair (target.comp Primrec.fst)))
  have checked := Primrec.option_map (addressPrim.comp target) evaluated.to₂
  have accepted : Primrec (fun a : Input => (directAddress positive a.1 a.2.1 a.2.2).toNat) := by
    apply (Primrec.option_getD.comp checked (Primrec.const 0)).of_eq
    intro a
    cases label : addressView a.2.2 <;> simp [label,directAddress,Option.any]
  let V := List.Vector Nat 3
  have src : Primrec (fun v : V => v.head) := Primrec.vector_head
  have tail : Primrec (fun v : V => v.tail) := Primrec.vector_tail
  have cert := Primrec.vector_head.comp tail
  have dst := Primrec.vector_head.comp (Primrec.vector_tail.comp tail)
  obtain ⟨program,hs⟩ := Proof.allPrimitiveFunctions 3 _ (accepted.comp (src.pair (cert.pair dst)))
  exact ⟨program,fun src cert dst => hs (src ::ᵥ cert ::ᵥ dst ::ᵥ nil)⟩

theorem exact_ConcreteDirectClassAddressProgram : ConcreteDirectClassAddressProgram := by
  intro entries s
  exact exact_DirectClassAddressProgram _ (exact_AllFourProgramWitnesses entries s).2.2.1

#print axioms exact_DirectClassAddressProgram
#print axioms exact_ConcreteDirectClassAddressProgram

end LogicLineages.PersistentMarking.NumberedWindowDirectClassAddressProgramChecks
