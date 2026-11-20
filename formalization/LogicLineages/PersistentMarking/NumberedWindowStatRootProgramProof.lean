module
public import LogicLineages.PersistentMarking.NumberedWindowStatRootProgramTargets
import LogicLineages.PersistentMarking.NumberedWindowRankPrograms
import LogicLineages.PersistentMarking.NumberedWindowStatProgramProof
import LogicLineages.PersistentMarking.NumberedWindowMarkRootProgramProof
import LogicLineages.PersistentMarking.NumberedWindowPositivePathParserPrograms
import LogicLineages.PersistentMarking.NumberedWindowSyntaxShapePrograms
import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowStatRootProgramProof
open NumberedWindowStatRootProgramTargets NumberedWindowStatRootAlgorithm NumberedWindowRankPrograms
open NumberedWindowPositivePathParserPrograms (equalPrim)
open NumberedWindowSyntaxShapePrograms (anyOption)
open NumberedWindowMarkRootProgramProof (guardPrim readPrim)
open LogicLineages.ComputabilityKnowledge List.Vector

abbrev Input := Nat × Nat × Nat
abbrev Node := Nat × List Nat

private theorem rowsPrim (xs heads) :
    Primrec (fun x : Nat × Node × Node => rows xs heads x.1 x.2.1 x.2.2) := by
  let P := Nat × Node × Node
  have q : Primrec (fun x : P => x.2.1) := Primrec.fst.comp Primrec.snd
  have r : Primrec (fun x : P => x.2.2) := Primrec.snd.comp Primrec.snd
  let a (i : Nat) := (Primrec.list_getD 0).comp (Primrec.snd.comp q) (Primrec.const i)
  let dest (i : Nat) := (Primrec.list_getD 0).comp (Primrec.snd.comp r) (Primrec.const i)
  have guard := Primrec.and.comp (Primrec.and.comp (equalPrim.comp (Primrec.fst.comp q) (Primrec.const 5))
    (equalPrim.comp (Primrec.fst.comp r) (Primrec.const 4))) (Primrec.not.comp (equalPrim.comp (a 2) (Primrec.const 0)))
  have target := allowedPrim false xs heads (a 1) (a 0) (dest 0)
  have repl := NumberedWindowStatProgramProof.replacementPrim.comp ((a 3).pair (Primrec.fst.pair (dest 1)))
  exact Primrec.and.comp guard (Primrec.and.comp target repl)

theorem statPrim (xs heads) : Primrec (fun x : Input => stat xs heads x.2.1 x.1 x.2.2) := by
  have part : Primrec (fun x : Input => x.2.1) := Primrec.fst.comp Primrec.snd
  have dst : Primrec (fun x : Input => x.2.2) := Primrec.snd.comp Primrec.snd
  let P := (Input × Node) × Node
  have x : Primrec (fun z : P => z.1.1) := Primrec.fst.comp Primrec.fst
  have q : Primrec (fun z : P => z.1.2) := Primrec.snd.comp Primrec.fst
  have row := (rowsPrim xs heads).comp ((part.comp x).pair (q.pair Primrec.snd))
  exact guardPrim Primrec.fst dst (anyOption (readPrim.comp Primrec.fst) (anyOption
    (readPrim.comp (dst.comp Primrec.fst)) row.to₂).to₂)

theorem program : StatRootProgram := by
  intro xs heads
  have a : Primrec (fun v : List.Vector Nat 3 => v.head) := Primrec.vector_head
  have tail : Primrec (fun v : List.Vector Nat 3 => v.tail) := Primrec.vector_tail
  have f := (statPrim xs heads).comp (a.pair ((Primrec.vector_head.comp tail).pair
    (Primrec.vector_head.comp (Primrec.vector_tail.comp tail))))
  have bit {α} [Primcodable α] {g : α → Bool} (hg : Primrec g) : Primrec (fun x => (g x).toNat) :=
    (Primrec.cond hg (Primrec.const 1) (Primrec.const 0)).of_eq (fun x => by cases h : g x <;> simp [h])
  obtain ⟨p,eval⟩ := GorbowPRProgram.Proof.allPrimitiveFunctions 3 _ (bit f)
  exact ⟨p,fun q part r => eval (q ::ᵥ part ::ᵥ r ::ᵥ List.Vector.nil)⟩
end LogicLineages.PersistentMarking.NumberedWindowStatRootProgramProof
