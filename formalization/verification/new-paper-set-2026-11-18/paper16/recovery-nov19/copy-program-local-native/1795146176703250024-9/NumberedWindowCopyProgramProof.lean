module
public import LogicLineages.PersistentMarking.NumberedWindowCopyProgramTargets
import LogicLineages.PersistentMarking.NumberedWindowRankPrograms
import LogicLineages.PersistentMarking.NumberedWindowOwnerPrograms
import LogicLineages.PersistentMarking.NumberedWindowMarkRootProgramProof
import LogicLineages.PersistentMarking.NumberedWindowHeadDeclarationPrograms
import LogicLineages.PersistentMarking.NumberedWindowPositivePathParserPrograms
import LogicLineages.PersistentMarking.NumberedWindowSyntaxShapePrograms
import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowCopyProgramProof
open NumberedWindowCopyProgramTargets NumberedWindowCopyAlgorithm NumberedWindowRankPrograms
open NumberedWindowPositivePathParserPrograms (equalPrim)
open NumberedWindowSyntaxShapePrograms (anyOption)
open NumberedWindowMarkRootProgramProof (guardPrim readPrim)
open LogicLineages.ComputabilityKnowledge List.Vector

abbrev Node := Nat × List Nat

private theorem rows (xs heads) : Primrec₂ (copyRows xs heads) := by
  let P := Node × Node
  have qt : Primrec (fun x : P => x.1.1) := Primrec.fst.comp Primrec.fst
  have rt : Primrec (fun x : P => x.2.1) := Primrec.fst.comp Primrec.snd
  have qfs : Primrec (fun x : P => x.1.2) := Primrec.snd.comp Primrec.fst
  have rfs : Primrec (fun x : P => x.2.2) := Primrec.snd.comp Primrec.snd
  let a (i : Nat) := (Primrec.list_getD 0).comp qfs (Primrec.const i)
  let dest (i : Nat) := (Primrec.list_getD 0).comp rfs (Primrec.const i)
  have guard := Primrec.and.comp (Primrec.and.comp (equalPrim.comp qt (Primrec.const 5))
    (equalPrim.comp rt (Primrec.const 4))) (Primrec.not.comp (equalPrim.comp (a 2) (Primrec.const 0)))
  have target := allowedPrim true xs heads (a 1) (a 0) (dest 0)
  have domains := Primrec.snd.comp (NumberedWindowHeadDeclarationPrograms.declarationPrim.comp (dest 0))
  have tuple := NumberedWindowOwnerPrograms.copiesPrim (a 0) (Primrec.pred.comp (a 2)) (a 3) (a 4) domains
  exact Primrec.and.comp guard (Primrec.and.comp target (equalPrim.comp tuple (dest 1)))

theorem copyPrim (xs heads) : Primrec₂ (copy xs heads) := by
  have inner := anyOption (readPrim.comp (Primrec.snd.comp
    (Primrec.fst : Primrec (Prod.fst : (Nat × Nat) × Node → _))))
    ((rows xs heads).comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂
  exact guardPrim Primrec.fst Primrec.snd (anyOption (readPrim.comp Primrec.fst) inner.to₂)

theorem program : CopyProgram := by
  intro xs heads
  have a : Primrec (fun v : List.Vector Nat 2 => v.head) := Primrec.vector_head
  have b := Primrec.vector_head.comp (Primrec.vector_tail : Primrec (fun v : List.Vector Nat 2 => v.tail))
  have f := (copyPrim xs heads).comp a b
  have bits : Primrec (fun v : List.Vector Nat 2 => (copy xs heads v.head v.tail.head).toNat) :=
    (Primrec.cond f (Primrec.const 1) (Primrec.const 0)).of_eq
      (fun v => by cases h : copy xs heads v.head v.tail.head <;> simp [h])
  obtain ⟨p,eval⟩ := GorbowPRProgram.Proof.allPrimitiveFunctions 2 _ bits
  exact ⟨p,fun q r => eval (q ::ᵥ r ::ᵥ List.Vector.nil)⟩
end LogicLineages.PersistentMarking.NumberedWindowCopyProgramProof
