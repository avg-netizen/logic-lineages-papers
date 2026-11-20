module
public import LogicLineages.PersistentMarking.NumberedWindowBinderRootProgramTargets
import LogicLineages.PersistentMarking.NumberedWindowFreshRootPrograms
import LogicLineages.PersistentMarking.NumberedWindowSingletonProgramProof
import LogicLineages.PersistentMarking.NumberedWindowPositivePathParserPrograms
import LogicLineages.PersistentMarking.NumberedWindowMarkRootProgramProof
import LogicLineages.PersistentMarking.NumberedWindowSyntaxShapePrograms
import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowBinderRootProgramProof
open NumberedWindowBinderRootProgramTargets NumberedWindowBinderRootAlgorithm
open NumberedWindowMarkRootProgramProof (guardPrim readPrim)
open NumberedWindowPositivePathParserPrograms (equalPrim)
open NumberedWindowSyntaxShapePrograms (anyOption)
open NumberedWindowFreshRootPrograms (Node fabsPrim)
open LogicLineages.ComputabilityKnowledge List.Vector

theorem betaPrim : Primrec₂ beta := by
  let P := (Nat × Nat) × Node
  have src : Primrec (fun x : P => x.2) := Primrec.snd
  have target : Primrec (fun x : P => x.1.2) := Primrec.snd.comp Primrec.fst
  let val {α} [Primcodable α] {node : α → Node} (hn : Primrec node) (i : Nat) :=
    (Primrec.list_getD 0).comp (Primrec.snd.comp hn) (Primrec.const i)
  let Q := P × Node
  have row : Primrec (fun x : Q => x.1.2) := Primrec.snd.comp Primrec.fst
  have fn : Primrec (fun x : Q => x.2) := Primrec.snd
  have tags := Primrec.and.comp (equalPrim.comp (Primrec.fst.comp row) (Primrec.const 6))
    (equalPrim.comp (Primrec.fst.comp fn) (Primrec.const 2))
  have dom := equalPrim.comp (val row 0) (val fn 0)
  have substituted := Primrec.fst.comp (NumberedWindowSingletonProgramProof.outputPrim.comp
    ((val row 3).pair ((Primrec.const 0).pair (val fn 1))))
  have dest := (target.comp Primrec.fst).comp Primrec.fst
  have test := Primrec.and.comp (Primrec.and.comp tags dom)
    (anyOption substituted (equalPrim.comp Primrec.snd dest).to₂)
  exact guardPrim Primrec.fst Primrec.snd (anyOption (readPrim.comp Primrec.fst)
    (anyOption (readPrim.comp (val src 2)) test.to₂).to₂)

private theorem binary {f} (hf : Primrec₂ f) : NumberedWindowMarkRootProgramTargets.BinaryProgram f := by
  have a : Primrec (fun v : List.Vector Nat 2 => v.head) := Primrec.vector_head
  have b := Primrec.vector_head.comp (Primrec.vector_tail : Primrec (fun v : List.Vector Nat 2 => v.tail))
  have bit := (Primrec.cond (hf.comp a b) (Primrec.const 1) (Primrec.const 0)).of_eq
    (g := fun v : List.Vector Nat 2 => (f v.head v.tail.head).toNat)
    (fun v => by cases h : f v.head v.tail.head <;> simp [h])
  obtain ⟨p,eval⟩ := GorbowPRProgram.Proof.allPrimitiveFunctions 2 _ bit
  exact ⟨p,fun q r => eval (q ::ᵥ r ::ᵥ List.Vector.nil)⟩

theorem programs : BinderRootPrograms := ⟨binary fabsPrim,binary betaPrim⟩
end LogicLineages.PersistentMarking.NumberedWindowBinderRootProgramProof
