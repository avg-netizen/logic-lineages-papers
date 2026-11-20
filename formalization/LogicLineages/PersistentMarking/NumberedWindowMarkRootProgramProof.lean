module

public import LogicLineages.PersistentMarking.NumberedWindowMarkRootProgramTargets
import LogicLineages.PersistentMarking.NumberedWindowAnnotationProgramProof
import LogicLineages.PersistentMarking.NumberedWindowHeadDeclarationPrograms
import LogicLineages.PersistentMarking.NumberedWindowLexicalRequirementPrograms
import LogicLineages.PersistentMarking.NumberedWindowSyntaxProgramProof
import LogicLineages.PersistentMarking.NumberedWindowFieldProgramChecks
import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowMarkRootProgramProof
open LogicLineages.ComputabilityKnowledge NumberedWindowMarkRootAlgorithm NumberedWindowMarkRootProgramTargets
open NumberedWindowLexicalRequirementPrograms (eqBool)
open NumberedWindowSyntaxShapePrograms (anyOption)
open NumberedWindowFieldAlgorithm (packNode unpackNode)
open List.Vector

theorem nodePrim : Primrec₂ packNode := by
  obtain ⟨p,eval⟩ := NumberedWindowFieldProgramChecks.exact_TaggedNodePrograms.1
  apply ((GorbowPRProgram.Proof.primitiveEvaluation 2 p).comp
    (Primrec.vector_cons.comp Primrec.fst (Primrec.vector_cons.comp (Primrec.encode.comp Primrec.snd)
      (Primrec.const List.Vector.nil)))).of_eq
  rintro ⟨i,fs⟩
  exact eval i fs

theorem readPrim : Primrec unpackNode := Primrec.encode_iff.mp
  ((GorbowPRProgram.Proof.unaryCorrespondence _).mpr NumberedWindowFieldProgramChecks.exact_TaggedNodePrograms.2)

theorem guardPrim {α} [Primcodable α] {a b : α → Nat} {v : α → Bool}
    (ha : Primrec a) (hb : Primrec b) (hv : Primrec v) : Primrec (fun x => guarded (a x) (b x) (v x)) :=
  Primrec.and.comp (Primrec.and.comp (Primrec.fst.comp (NumberedWindowSyntaxProgramProof.bits.comp ha))
    (Primrec.fst.comp (NumberedWindowSyntaxProgramProof.bits.comp hb))) hv

private theorem owner {α} [Primcodable α] {f t k bs es : α → Nat} (hf : Primrec f)
    (ht : Primrec t) (hk : Primrec k) (hb : Primrec bs) (he : Primrec es) :
    Primrec (fun x => packNode 5 [f x,t x,k x,bs x,es x]) :=
  nodePrim.comp (Primrec.const 5) (Primrec.list_cons.comp hf (Primrec.list_cons.comp ht
    (Primrec.list_cons.comp hk (Primrec.list_cons.comp hb (Primrec.list_cons.comp he (Primrec.const []))))))

theorem markPrim : Primrec (fun p : Nat × Nat × Nat => mark p.1 p.2.1 p.2.2) := by
  let P := Nat × Nat × Nat
  have src : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
  have dst : Primrec (fun p : P => p.2.2) := Primrec.snd.comp Primrec.snd
  let Q := P × Nat × List Nat
  have tag : Primrec (fun p : Q => p.2.1) := Primrec.fst.comp Primrec.snd
  have fs : Primrec (fun p : Q => p.2.2) := Primrec.snd.comp Primrec.snd
  have f := (Primrec.list_getD 0).comp fs (Primrec.const 0)
  have bs := (Primrec.list_getD 0).comp fs (Primrec.const 1)
  have expected := owner f (Primrec.fst.comp (NumberedWindowHeadDeclarationPrograms.declarationPrim.comp f))
    (Primrec.fst.comp Primrec.fst) bs (Primrec.const 0)
  exact guardPrim src dst (anyOption (readPrim.comp src)
    (Primrec.and.comp (eqBool.comp tag (Primrec.const 4)) (eqBool.comp expected (dst.comp Primrec.fst))).to₂)

theorem lowerPrim : Primrec₂ lower := by
  let Q := (Nat × Nat) × Nat × List Nat
  have tag : Primrec (fun p : Q => p.2.1) := Primrec.fst.comp Primrec.snd
  have fs : Primrec (fun p : Q => p.2.2) := Primrec.snd.comp Primrec.snd
  let atIndex (n : Nat) := (Primrec.list_getD 0).comp fs (Primrec.const n)
  have expected := owner (atIndex 0) (atIndex 1) (Primrec.pred.comp (atIndex 2)) (atIndex 3) (atIndex 4)
  have guard := Primrec.and.comp (eqBool.comp tag (Primrec.const 5))
    (Primrec.not.comp (eqBool.comp (atIndex 2) (Primrec.const 0)))
  exact guardPrim Primrec.fst Primrec.snd (anyOption (readPrim.comp Primrec.fst)
    (Primrec.and.comp guard (eqBool.comp expected (Primrec.snd.comp Primrec.fst))).to₂)

theorem bottomPrim : Primrec₂ bottom := by
  have ty := Primrec.fst.comp (NumberedWindowAnnotationProgramProof.annotationPrim.comp
    (Primrec.fst : Primrec (Prod.fst : Nat × Nat → _)))
  have target := nodePrim.comp (Primrec.const 3) (Primrec.list_cons.comp ty (Primrec.const []))
  exact guardPrim Primrec.fst Primrec.snd
    (Primrec.and.comp (Primrec.not.comp (eqBool.comp Primrec.fst target)) (eqBool.comp target Primrec.snd))

private theorem indicator {α} [Primcodable α] {f : α → Bool} (hf : Primrec f) :
    Primrec (fun x => (f x).toNat) :=
  (Primrec.cond hf (Primrec.const 1) (Primrec.const 0)).of_eq (fun x => by cases h : f x <;> simp [h])

private theorem bin {f} (h : Primrec₂ f) : BinaryProgram f := by
  have a : Primrec (fun v : List.Vector Nat 2 => v.head) := Primrec.vector_head
  have b := Primrec.vector_head.comp (Primrec.vector_tail : Primrec (fun v : List.Vector Nat 2 => v.tail))
  obtain ⟨p,e⟩ := GorbowPRProgram.Proof.allPrimitiveFunctions 2 _ (indicator (h.comp a b))
  exact ⟨p,fun q r => e (q ::ᵥ r ::ᵥ List.Vector.nil)⟩

theorem programs : SimpleRootPrograms := by
  have k : Primrec (fun v : List.Vector Nat 3 => v.head) := Primrec.vector_head
  have q := Primrec.vector_head.comp (Primrec.vector_tail : Primrec (fun v : List.Vector Nat 3 => v.tail))
  have r := Primrec.vector_head.comp (Primrec.vector_tail.comp (Primrec.vector_tail : Primrec (fun v : List.Vector Nat 3 => v.tail)))
  obtain ⟨p,e⟩ := GorbowPRProgram.Proof.allPrimitiveFunctions 3 _ (indicator (markPrim.comp (k.pair (q.pair r))))
  exact ⟨⟨p,fun n a b => e (n ::ᵥ a ::ᵥ b ::ᵥ List.Vector.nil)⟩,bin lowerPrim,bin bottomPrim⟩
end LogicLineages.PersistentMarking.NumberedWindowMarkRootProgramProof
