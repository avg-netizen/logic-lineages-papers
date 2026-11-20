module

public import LogicLineages.PersistentMarking.NumberedWindowSelectProgramTargets
import LogicLineages.PersistentMarking.NumberedWindowOwnerPrograms
import LogicLineages.PersistentMarking.NumberedWindowMarkRootProgramProof
import LogicLineages.PersistentMarking.NumberedWindowAnnotationProgramProof
import LogicLineages.PersistentMarking.NumberedWindowPositivePathParserPrograms
import LogicLineages.PersistentMarking.NumberedWindowSyntaxShapePrograms
import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowSelectProgramProof
open NumberedWindowSelectAlgorithm NumberedWindowSelectProgramTargets NumberedWindowOwnerPrograms
open NumberedWindowPositivePathParserPrograms (fieldsPrim equalPrim)
open NumberedWindowSyntaxShapePrograms (anyOption)
open LogicLineages.ComputabilityKnowledge List.Vector

private theorem chosenPrim {α} [Primcodable α] {ex : α → Bool} {i b e : α → Nat}
    (hx : Primrec ex) (hi : Primrec i) (hb : Primrec b) (he : Primrec e) :
    Primrec (fun x => chosen (ex x) (i x) (b x) (e x)) :=
  Primrec.option_bind (fieldsPrim.comp (Primrec.cond hx he hb))
    (Primrec.list_getElem?.comp Primrec.snd (hi.comp Primrec.fst)).to₂

private theorem fromOwnerPrim {α} [Primcodable α] {ex : α → Bool} {ds : α → List Nat}
    {i dst f t k b e : α → Nat} (hx : Primrec ex) (hi : Primrec i) (hs : Primrec ds)
    (hr : Primrec dst) (hf : Primrec f) (ht : Primrec t) (hk : Primrec k) (hb : Primrec b) (he : Primrec e) :
    Primrec (fun x => fromOwner (ex x) (i x) (ds x) (dst x) (f x) (t x) (k x) (b x) (e x)) := by
  have route := planPrim.comp ht hs
  have pred := Primrec.pred.comp hk
  have selected := chosenPrim hx hi hb he
  let P := α × Nat
  have q : Primrec (fun x : P => x.2) := Primrec.snd
  have ann := Primrec.fst.comp (NumberedWindowAnnotationProgramProof.annotationPrim.comp q)
  have code := applyPrim (hf.comp Primrec.fst) (pred.comp Primrec.fst) (hb.comp Primrec.fst)
    (he.comp Primrec.fst) q ((Primrec.snd.comp route).comp Primrec.fst)
  exact Primrec.and.comp (Primrec.not.comp (equalPrim.comp hk (Primrec.const 0)))
    (anyOption selected (Primrec.and.comp (equalPrim.comp ann ((Primrec.fst.comp route).comp Primrec.fst))
      (equalPrim.comp code (hr.comp Primrec.fst))).to₂)

abbrev Input := Parameters × Nat × Nat

theorem selectPrim : Primrec (fun p : Input => select p.1.1 p.1.2.1 p.1.2.2 p.2.1 p.2.2) := by
  have ex : Primrec (fun p : Input => p.1.1) := Primrec.fst.comp Primrec.fst
  have idx : Primrec (fun p : Input => p.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have ds : Primrec (fun p : Input => p.1.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have src : Primrec (fun p : Input => p.2.1) := Primrec.fst.comp Primrec.snd
  have dst : Primrec (fun p : Input => p.2.2) := Primrec.snd.comp Primrec.snd
  let P := Input × Nat × List Nat
  have tag : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
  have fs : Primrec (fun p : P => p.2.2) := Primrec.snd.comp Primrec.snd
  let val (n : Nat) := (Primrec.list_getD 0).comp fs (Primrec.const n)
  have matches := fromOwnerPrim (ex.comp Primrec.fst) (idx.comp Primrec.fst) (ds.comp Primrec.fst)
    (dst.comp Primrec.fst) (val 0) (val 1) (val 2) (val 3) (val 4)
  exact NumberedWindowMarkRootProgramProof.guardPrim src dst (anyOption
    (NumberedWindowMarkRootProgramProof.readPrim.comp src) (Primrec.and.comp
      (equalPrim.comp tag (Primrec.const 5)) matches).to₂)

theorem program : SelectProgram := by
  let read (n : Nat) := (Encodable.decode (α := Parameters) n).getD default
  have readP : Primrec read := Primrec.option_getD.comp Primrec.decode (Primrec.const default)
  have a : Primrec (fun v : List.Vector Nat 3 => v.head) := Primrec.vector_head
  have tail : Primrec (fun v : List.Vector Nat 3 => v.tail) := Primrec.vector_tail
  have flag := selectPrim.comp ((readP.comp a).pair
    ((Primrec.vector_head.comp tail).pair (Primrec.vector_head.comp (Primrec.vector_tail.comp tail))))
  have bit {α} [Primcodable α] {g : α → Bool} (hg : Primrec g) : Primrec (fun x => (g x).toNat) :=
    (Primrec.cond hg (Primrec.const 1) (Primrec.const 0)).of_eq (fun x => by cases h : g x <;> simp [h])
  obtain ⟨p,eval⟩ := GorbowPRProgram.Proof.allPrimitiveFunctions 3 _ (bit flag)
  refine ⟨p,?_⟩
  intro params q r
  have hr : read (Encodable.encode params) = params := by
    simp only [read,Encodable.encodek,Option.getD_some]
  have h := eval (Encodable.encode params ::ᵥ q ::ᵥ r ::ᵥ List.Vector.nil)
  change _ = (select (read (Encodable.encode params)).1 (read (Encodable.encode params)).2.1
    (read (Encodable.encode params)).2.2 q r).toNat at h
  rwa [hr] at h
end LogicLineages.PersistentMarking.NumberedWindowSelectProgramProof
