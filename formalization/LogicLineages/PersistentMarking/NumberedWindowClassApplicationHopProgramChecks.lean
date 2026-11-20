module

public import LogicLineages.PersistentMarking.NumberedWindowClassApplicationHopProgramTargets
import LogicLineages.PersistentMarking.NumberedWindowRawApplicationLiftProgramChecks
import LogicLineages.PersistentMarking.NumberedWindowPositivePathParserPrograms
import LogicLineages.PersistentMarking.NumberedWindowMarkRootProgramProof
import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowClassApplicationHopProgramChecks
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowPositivePathAlgorithm (RawEdge ClassHop hopView)
open NumberedWindowFieldAlgorithm (packNode)
open NumberedWindowClassApplicationHop NumberedWindowClassApplicationHopProgramTargets
open NumberedWindowRawApplicationLift NumberedWindowRawApplicationLiftProgramChecks
open NumberedWindowMarkRootProgramProof (nodePrim)
open NumberedWindowPositivePathParserPrograms (hopPrim)

abbrev Config := Nat × Nat × Nat

private theorem rawPrim : Primrec (fun p : Config × RawEdge =>
    lift p.1.1 p.1.2.1 p.1.2.2 p.2.1 p.2.2.1 p.2.2.2) := by
  let P := Config × RawEdge
  have d : Primrec (fun p : P => p.1.1) := Primrec.fst.comp Primrec.fst
  have c : Primrec (fun p : P => p.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have a : Primrec (fun p : P => p.1.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have q : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
  have w : Primrec (fun p : P => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have r : Primrec (fun p : P => p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have args := Primrec.vector_cons.comp d (Primrec.vector_cons.comp c
    (Primrec.vector_cons.comp a (Primrec.vector_cons.comp q (Primrec.vector_cons.comp w
      (Primrec.vector_cons.comp r (Primrec.const List.Vector.nil))))))
  obtain ⟨program,h⟩ := exact_RawApplicationLiftProgram
  apply Primrec.encode_iff.mp
  exact ((Proof.primitiveEvaluation 6 program).comp args).of_eq
    (fun p => h p.1.1 p.1.2.1 p.1.2.2 p.2.1 p.2.2.1 p.2.2.2)

private def closeHop (least : Nat → Option Nat) (p : RawEdge) :
    Option (Nat × Nat × Nat) := do
  let x ← least p.1
  let y ← least p.2.2
  pure (x,y,packNode 2 [y,packNode 1 [p.1,p.2.2,p.2.1]])

private theorem closePrim (least : Nat → Option Nat) (hl : Primrec least) :
    Primrec (closeHop least) := by
  let P := (RawEdge × Nat) × Nat
  have rawQ : Primrec (fun p : P => p.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have tail : Primrec (fun p : P => p.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have rawR := Primrec.snd.comp tail
  have rawW := Primrec.fst.comp tail
  have newQ : Primrec (fun p : P => p.1.2) := Primrec.snd.comp Primrec.fst
  have newR : Primrec (fun p : P => p.2) := Primrec.snd
  have edge := nodePrim.comp (Primrec.const 1) (Primrec.list_cons.comp rawQ
    (Primrec.list_cons.comp rawR (Primrec.list_cons.comp rawW (Primrec.const []))))
  have hop := nodePrim.comp (Primrec.const 2)
    (Primrec.list_cons.comp newR (Primrec.list_cons.comp edge (Primrec.const [])))
  have finish := Primrec.option_some.comp (newQ.pair (newR.pair hop))
  have afterSource := Primrec.option_bind
    (hl.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst : Primrec (Prod.fst : RawEdge × Nat → RawEdge)))))
    finish.to₂
  exact Primrec.option_bind (hl.comp Primrec.fst) afterSource.to₂

theorem liftHopPrim (least : Nat → Option Nat) (hl : Primrec least) :
    Primrec (fun p : Config × Nat => liftHop least p.1.1 p.1.2.1 p.1.2.2 p.2) := by
  let Input := Config × Nat
  have data : Primrec (fun p : Input × ClassHop => (p.1.1,p.2.2)) :=
    (Primrec.fst.comp Primrec.fst).pair (Primrec.snd.comp Primrec.snd)
  have onHop := (closePrim least hl).comp (rawPrim.comp data)
  apply (Primrec.option_bind (hopPrim.comp (Primrec.snd : Primrec (Prod.snd : Input → Nat)))
    onHop.to₂).of_eq
  intro i
  unfold liftHop
  cases hopView i.2 with
  | none => rfl
  | some hop =>
    rcases hop with ⟨target,q,w,r⟩
    rfl

theorem exact_ClassHopLiftProgram : ClassHopLiftProgram := by
  intro least hl
  let V := List.Vector Nat 4
  have d : Primrec (fun v : V => v.head) := Primrec.vector_head
  have td : Primrec (fun v : V => v.tail) := Primrec.vector_tail
  have c := Primrec.vector_head.comp td
  have tc := Primrec.vector_tail.comp td
  have a := Primrec.vector_head.comp tc
  have ta := Primrec.vector_tail.comp tc
  have code := Primrec.vector_head.comp ta
  have program := (liftHopPrim least hl).comp ((d.pair (c.pair a)).pair code)
  obtain ⟨p,h⟩ := Proof.allPrimitiveFunctions 4 _ (Primrec.encode.comp program)
  exact ⟨p,fun d c a code => h (d ::ᵥ c ::ᵥ a ::ᵥ code ::ᵥ nil)⟩

#print axioms exact_ClassHopLiftProgram

end LogicLineages.PersistentMarking.NumberedWindowClassApplicationHopProgramChecks
