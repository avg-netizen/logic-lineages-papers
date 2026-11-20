module

public import LogicLineages.PersistentMarking.NumberedWindowSyntaxProgramTargets
import LogicLineages.PersistentMarking.NumberedWindowAddressProgramProof
import LogicLineages.PersistentMarking.NumberedWindowProgramKernelChecks
import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowSyntaxShapePrograms
open LogicLineages.ComputabilityKnowledge NumberedWindowSyntaxAlgorithm NumberedWindowAddressAlgorithm
open NumberedWindowAddressProgramProof (validType)

theorem pairs : Primrec NumberedWindowPairAlgorithm.decode := Primrec.encode_iff.mp
  ((GorbowPRProgram.Proof.unaryCorrespondence _).mpr NumberedWindowProgramKernelChecks.completeDecoding)

theorem anyOption {α β} [Primcodable α] [Primcodable β] {f : α → Option β} {g : α → β → Bool}
    (hf : Primrec f) (hg : Primrec₂ g) : Primrec (fun a => (f a).any (fun b => g a b)) :=
  (Primrec.option_getD.comp (Primrec.option_map hf hg) (Primrec.const false)).of_eq
    (fun a => by cases h : f a <;> simp [h])

private theorem selectTag {α} [Primcodable α] {tag : α → Nat} (ht : Primrec tag)
    (n : Nat) {f g : α → Bool} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => if tag a = n then f a else g a) :=
  Primrec.ite (Primrec.eq.comp ht (Primrec.const n)) hf hg

private theorem headPartsPrim : Primrec₂ headParts := by
  let code := (Prod.snd : Nat × Nat → Nat)
  have h0 : Primrec (fun p : Nat × Nat => code p == 0) :=
    ((Primrec.eq.comp Primrec.snd (Primrec.const 0)).decide).of_eq (fun _ => by simp [code])
  have ty : Primrec (fun p : Nat × Nat => typeBit (code p)) := validType.comp Primrec.snd
  have pair := pairs.comp (Primrec.snd : Primrec code)
  have app := anyOption pair (Primrec.and.comp (validType.comp (Primrec.fst.comp Primrec.snd))
    (validType.comp (Primrec.snd.comp Primrec.snd))).to₂
  have tag : Primrec (Prod.fst : Nat × Nat → Nat) := Primrec.fst
  apply (selectTag tag 0 h0 (selectTag tag 1 h0 (selectTag tag 2 ty (selectTag tag 3 ty
    (selectTag tag 4 app (selectTag tag 5 (Primrec.option_isSome.comp pair) (Primrec.const false))))))).of_eq
  rintro ⟨tag,p⟩
  rcases tag with _ | _ | _ | _ | _ | _ | tag <;> simp [headParts, code]

theorem headPrim : Primrec headBit :=
  anyOption pairs (headPartsPrim.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂

private inductive Slot where
  | literal | type | head | term | args

private def field : Slot → List Row → Nat → Bool
  | .literal, _, _ => true
  | .type, _, n => typeBit n
  | .head, _, n => headBit n
  | .term, t, n => (t.getD n (false,false)).1
  | .args, t, n => (t.getD n (false,false)).2

private theorem fieldPrim : ∀ k, Primrec₂ (field k)
  | .literal => Primrec.const true
  | .type => validType.comp Primrec.snd
  | .head => headPrim.comp Primrec.snd
  | .term => Primrec.fst.comp (Primrec.list_getD (false,false))
  | .args => Primrec.snd.comp (Primrec.list_getD (false,false))

private def layout : List Slot → List Row → List Nat → Bool
  | [], _, xs => xs.isEmpty
  | _ :: _, _, [] => false
  | k :: ks,t,n :: ns => field k t n && layout ks t ns

private theorem layoutPrim : ∀ ks, Primrec₂ (layout ks) := by
  intro ks
  induction ks with
  | nil =>
    apply ((Primrec.eq.comp Primrec.snd (Primrec.const [])).decide).of_eq
    rintro ⟨t,xs⟩
    cases xs <;> rfl
  | cons k ks ih =>
    have empty := (Primrec.eq.comp (Primrec.snd : Primrec (Prod.snd : List Row × List Nat → List Nat))
      (Primrec.const [])).decide
    have first := (fieldPrim k).comp Primrec.fst (Primrec.list_headI.comp Primrec.snd)
    have tail := ih.comp Primrec.fst (Primrec.list_tail.comp Primrec.snd)
    apply (Primrec.cond empty (Primrec.const false) (Primrec.and.comp first tail)).of_eq
    rintro ⟨t,xs⟩
    cases xs <;> rfl

theorem partsPrim : Primrec (fun p : List Row × Nat × List Nat => termParts
    (fun q => (p.1.getD q (false,false)).1) (fun a => (p.1.getD a (false,false)).2) p.2.1 p.2.2) := by
  let test (ks : List Slot) := (layoutPrim ks).comp (Primrec.fst : Primrec (Prod.fst : List Row × Nat × List Nat → List Row))
    (Primrec.snd.comp Primrec.snd)
  have tag : Primrec (fun p : List Row × Nat × List Nat => p.2.1) := Primrec.fst.comp Primrec.snd
  open Slot in
    apply (selectTag tag 0 (test [type,literal]) (selectTag tag 1 (test [type,literal])
      (selectTag tag 2 (test [type,term]) (selectTag tag 3 (test [type])
        (selectTag tag 4 (test [head,args]) (selectTag tag 5 (test [head,type,literal,args,args])
          (selectTag tag 6 (test [type,type,term,term]) (Primrec.const false)))))))).of_eq
  rintro ⟨t,tag,xs⟩
  rcases tag with _ | _ | _ | _ | _ | _ | _ | tag
  all_goals rcases xs with _ | ⟨a,_ | ⟨b,_ | ⟨c,_ | ⟨d,_ | ⟨e,_ | ⟨v,vs⟩⟩⟩⟩⟩⟩ <;>
    simp [layout,field,termParts]

end LogicLineages.PersistentMarking.NumberedWindowSyntaxShapePrograms
