module

public import LogicLineages.PersistentMarking.NumberedWindowExchangePartPrograms
import LogicLineages.PersistentMarking.NumberedWindowLexicalRequirementPrograms
import LogicLineages.PersistentMarking.NumberedWindowSyntaxProgramProof
import LogicLineages.PersistentMarking.NumberedWindowFieldProgramChecks
import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowExchangeProgramProof
open LogicLineages.ComputabilityKnowledge NumberedWindowExchangeAlgorithm NumberedWindowExchangePartPrograms
open NumberedWindowExchangeAtoms NumberedWindowExchangeProgramTargets List.Vector
open NumberedWindowLexicalRequirementPrograms (eqBool)

private def consFields : Nat → Option (Nat × Nat)
  | 0 => none
  | n+1 => NumberedWindowPairAlgorithm.decode n

private theorem consFieldsPrim : Primrec consFields :=
  (Primrec.nat_casesOn Primrec.id (Primrec.const none) (NumberedWindowSyntaxShapePrograms.pairs.comp Primrec.snd).to₂).of_eq
    (fun n => by cases n <;> rfl)

abbrev Input := Env × Nat × Nat

private theorem termPrim : Primrec (fun p : Input => termNext p.1.1 p.1.2 p.2.1 p.2.2) := by
  have node : Primrec NumberedWindowFieldAlgorithm.unpackNode := Primrec.encode_iff.mp
    ((GorbowPRProgram.Proof.unaryCorrespondence _).mpr NumberedWindowFieldProgramChecks.exact_TaggedNodePrograms.2)
  exact anyTwo (node.comp (Primrec.fst.comp Primrec.snd)) (node.comp (Primrec.snd.comp Primrec.snd))
    (partsPrim.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd))

private theorem argsPrim : Primrec (fun p : Input => argsNext p.1.2 p.2.1 p.2.2) := by
  let P := Input × (Nat × Nat) × Nat × Nat
  have l : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
  have r : Primrec (fun p : P => p.2.2) := Primrec.snd.comp Primrec.snd
  have prev : Primrec (fun p : P => p.1.1.2) := Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have x := Primrec.fst.comp l
  have y := Primrec.fst.comp r
  have u := Primrec.snd.comp l
  have v := Primrec.snd.comp r
  have xy := Primrec.fst.comp ((Primrec.list_getD (false,false)).comp prev (pairPrim.comp x y))
  have uv := Primrec.snd.comp ((Primrec.list_getD (false,false)).comp prev (pairPrim.comp u v))
  apply (anyTwo (consFieldsPrim.comp (Primrec.fst.comp Primrec.snd)) (consFieldsPrim.comp (Primrec.snd.comp Primrec.snd))
    (Primrec.or.comp (Primrec.and.comp xy (eqBool.comp u v)) (Primrec.and.comp (eqBool.comp x y) uv))).of_eq
  rintro ⟨env,a,b⟩
  cases a <;> cases b <;> simp [consFields,argsNext]

private theorem nextPrim : Primrec₂ (fun (env : Env) k => next env.1 env.2 k) :=
  Primrec.option_getD.comp (Primrec.option_map (NumberedWindowSyntaxShapePrograms.pairs.comp Primrec.snd)
    ((termPrim.pair argsPrim).comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)).to₂) (Primrec.const (false,false))

private theorem tablePrim : Primrec₂ table := by
  have hp : Primrec (fun p : HeadPairs × Nat × List Row => p.1) := Primrec.fst
  have k : Primrec (fun p : HeadPairs × Nat × List Row => p.2.1) := Primrec.fst.comp Primrec.snd
  have prev : Primrec (fun p : HeadPairs × Nat × List Row => p.2.2) := Primrec.snd.comp Primrec.snd
  have step := Primrec.list_append.comp prev
    (Primrec.list_cons.comp (nextPrim.comp (hp.pair prev) k) (Primrec.const []))
  apply (Primrec.nat_rec (Primrec.const ([] : List Row)) step.to₂).of_eq
  intro hp n
  induction n with
  | zero => rfl
  | succ n ih => simp [table,ih]

theorem bitsPrim : Primrec (fun p : HeadPairs × Nat × Nat => bits p.1 p.2.1 p.2.2) := by
  let P := HeadPairs × Nat × Nat
  have hp : Primrec (Prod.fst : P → _) := Primrec.fst
  have a : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
  have b : Primrec (fun p : P => p.2.2) := Primrec.snd.comp Primrec.snd
  have k := pairPrim.comp a b
  have r := nextPrim.comp (hp.pair (tablePrim.comp hp k)) k
  have x := NumberedWindowSyntaxProgramProof.bits.comp a
  have y := NumberedWindowSyntaxProgramProof.bits.comp b
  exact (Primrec.and.comp (Primrec.and.comp (Primrec.fst.comp x) (Primrec.fst.comp y)) (Primrec.fst.comp r)).pair
    (Primrec.and.comp (Primrec.and.comp (Primrec.snd.comp x) (Primrec.snd.comp y)) (Primrec.snd.comp r))

private def readPairs (n : Nat) := ((Encodable.decode n : Option HeadPairs).getD [])

theorem program : ContextualExchangeProgram := by
  let V := List.Vector Nat 3
  have read : Primrec readPairs := Primrec.option_getD.comp Primrec.decode (Primrec.const [])
  have a := Primrec.vector_head.comp (Primrec.vector_tail : Primrec (fun v : V => v.tail))
  have b := Primrec.vector_head.comp (Primrec.vector_tail.comp (Primrec.vector_tail : Primrec (fun v : V => v.tail)))
  have compute := bitsPrim.comp ((read.comp Primrec.vector_head).pair (a.pair b))
  obtain ⟨p,e⟩ := GorbowPRProgram.Proof.allPrimitiveFunctions 3 _ (Primrec.encode.comp compute)
  exact ⟨p,fun hp a b => by simpa [readPairs] using e (Encodable.encode hp ::ᵥ a ::ᵥ b ::ᵥ List.Vector.nil)⟩
end LogicLineages.PersistentMarking.NumberedWindowExchangeProgramProof
