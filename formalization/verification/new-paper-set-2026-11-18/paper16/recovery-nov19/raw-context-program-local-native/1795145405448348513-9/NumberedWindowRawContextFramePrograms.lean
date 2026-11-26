module

public import LogicLineages.PersistentMarking.NumberedWindowRawContextFocusPrograms
import LogicLineages.PersistentMarking.NumberedWindowFieldProgramChecks
import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowRawContextFramePrograms
open LogicLineages.ComputabilityKnowledge NumberedWindowRawContextAlgorithm
open NumberedWindowRawContextFocusPrograms (focusPrim)
open NumberedWindowPositivePathParserPrograms (equalPrim)

abbrev Node := Nat × List Nat
private abbrev Input := Node × Node × Node

private def fits (wtag warity tag arity : Nat) (p : Input) : Prop :=
  p.1.1 = wtag ∧ p.1.2.length = warity ∧
    p.2.1.1 = tag ∧ p.2.1.2.length = arity ∧
    p.2.2.1 = tag ∧ p.2.2.2.length = arity

private instance (wtag warity tag arity) (p : Input) : Decidable (fits wtag warity tag arity p) := by
  unfold fits
  infer_instance

private theorem fitsPrim (wtag warity tag arity : Nat) : PrimrecPred (fits wtag warity tag arity) :=
  let w := (Primrec.fst : Primrec (Prod.fst : Input → Node))
  let q := (Primrec.fst.comp Primrec.snd : Primrec (fun p : Input => p.2.1))
  let r := (Primrec.snd.comp Primrec.snd : Primrec (fun p : Input => p.2.2))
  let sameTag (node : Input → Node) (h : Primrec node) (t : Nat) :=
    Primrec.eq.comp (Primrec.fst.comp h) (Primrec.const t)
  let sameArity (node : Input → Node) (h : Primrec node) (n : Nat) :=
    Primrec.eq.comp (Primrec.list_length.comp (Primrec.snd.comp h)) (Primrec.const n)
  (sameTag _ w wtag).and ((sameArity _ w warity).and ((sameTag _ q tag).and
    ((sameArity _ q arity).and ((sameTag _ r tag).and (sameArity _ r arity)))))

private def value (node : Node) (i : Nat) := node.2.getD i 0

private theorem valPrim (i : Nat) : Primrec (fun n => value n i) :=
  (Primrec.list_getD 0).comp Primrec.snd (Primrec.const i)

private def keep (ok : Bool) (frame : Option Frame) := if ok then frame else none

private theorem keepPrim : Primrec₂ keep :=
  Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const true)) Primrec.snd (Primrec.const none)

private def seek (p : Input) (slot : Nat) : Option Frame :=
  (focus (value p.1 0) (value p.2.1 slot) (value p.2.2 slot)).map
    (fun s => (s.1,value p.1 1,s.2))

private theorem seekPrim (slot : Nat) : Primrec (fun p => seek p slot) := by
  let q := (Primrec.fst.comp Primrec.snd : Primrec (fun p : Input => p.2.1))
  let r := (Primrec.snd.comp Primrec.snd : Primrec (fun p : Input => p.2.2))
  have index := (valPrim 0).comp (Primrec.fst : Primrec (Prod.fst : Input → Node))
  have focusHere := focusPrim.comp (index.pair (((valPrim slot).comp q).pair ((valPrim slot).comp r)))
  have witness := (valPrim 1).comp (Primrec.fst.comp Primrec.fst : Primrec (fun p : Input × Pair => p.1.1))
  exact Primrec.option_map focusHere ((Primrec.fst.comp Primrec.snd).pair
    (witness.pair (Primrec.snd.comp Primrec.snd))).to₂

private def same (p : Input) (i : Nat) := value p.2.1 i == value p.2.2 i

private theorem samePrim (i : Nat) : Primrec (fun p => same p i) :=
  equalPrim.comp ((valPrim i).comp (Primrec.fst.comp Primrec.snd))
    ((valPrim i).comp (Primrec.snd.comp Primrec.snd))

private def inner (p : Input) (i : Nat) : Option Frame :=
  some (value p.2.1 i,value p.1 0,value p.2.2 i)

private theorem innerPrim (i : Nat) : Primrec (fun p => inner p i) :=
  Primrec.option_some.comp (((valPrim i).comp (Primrec.fst.comp Primrec.snd)).pair
    (((valPrim 0).comp Primrec.fst).pair ((valPrim i).comp (Primrec.snd.comp Primrec.snd))))

private def compiled (p : Input) : Option Frame :=
  if fits 1 1 2 2 p then keep (same p 0) (inner p 1)
  else if fits 2 2 4 2 p then keep (same p 0) (seek p 1)
  else if fits 3 2 5 5 p then keep (same p 0 && same p 1 && same p 2 && same p 4) (seek p 3)
  else if fits 4 2 5 5 p then keep (same p 0 && same p 1 && same p 2 && same p 3) (seek p 4)
  else if fits 5 1 6 4 p then keep (same p 0 && same p 1 && same p 3) (inner p 2)
  else none

private theorem compiledPrim : Primrec compiled := by
  have base := Primrec.and.comp (Primrec.and.comp (samePrim 0) (samePrim 1)) (samePrim 2)
  have lower (slot other : Nat) :=
    keepPrim.comp (Primrec.and.comp base (samePrim other)) (seekPrim slot)
  have function := keepPrim.comp
    (Primrec.and.comp (Primrec.and.comp (samePrim 0) (samePrim 1)) (samePrim 3)) (innerPrim 2)
  exact Primrec.ite (fitsPrim 1 1 2 2) (keepPrim.comp (samePrim 0) (innerPrim 1))
    (Primrec.ite (fitsPrim 2 2 4 2) (keepPrim.comp (samePrim 0) (seekPrim 1))
      (Primrec.ite (fitsPrim 3 2 5 5) (lower 3 4)
        (Primrec.ite (fitsPrim 4 2 5 5) (lower 4 3)
          (Primrec.ite (fitsPrim 5 1 6 4) function (Primrec.const none)))))

private theorem fields3 {xs : List Nat} (h : xs.length = 3) : ∃ a b c, xs = [a,b,c] := by
  rcases xs with _ | ⟨a,_ | ⟨b,_ | ⟨c,_ | ⟨d,tail⟩⟩⟩⟩ <;> simp_all

private theorem fields4 {xs : List Nat} (h : xs.length = 4) : ∃ a b c d, xs = [a,b,c,d] := by
  rcases xs with _ | ⟨a,tail⟩
  · simp at h
  · obtain ⟨b,c,d,rfl⟩ := fields3 (by simpa using h)
    exact ⟨a,b,c,d,rfl⟩

private theorem fields5 {xs : List Nat} (h : xs.length = 5) : ∃ a b c d e, xs = [a,b,c,d,e] := by
  rcases xs with _ | ⟨a,tail⟩
  · simp at h
  · obtain ⟨b,c,d,e,rfl⟩ := fields4 (by simpa using h)
    exact ⟨a,b,c,d,e,rfl⟩

private theorem compare (p : Input) : compiled p = context p.1.1 p.1.2 p.2.1 p.2.2 := by
  rcases p with ⟨⟨wtag,ws⟩,⟨utag,us⟩,⟨vtag,vs⟩⟩
  unfold compiled
  split
  · rename_i h
    obtain ⟨rfl,hw,rfl,hu,rfl,hv⟩ := h
    obtain ⟨w,rfl⟩ := List.length_eq_one_iff.mp hw
    rw [List.eq_getElem_of_length_eq_two us hu,List.eq_getElem_of_length_eq_two vs hv]
    rfl
  split
  · rename_i h
    obtain ⟨rfl,hw,rfl,hu,rfl,hv⟩ := h
    rw [List.eq_getElem_of_length_eq_two ws hw,List.eq_getElem_of_length_eq_two us hu,
      List.eq_getElem_of_length_eq_two vs hv]
    rfl
  split
  · rename_i h
    obtain ⟨rfl,hw,rfl,hu,rfl,hv⟩ := h
    obtain ⟨f,s,k,bs,es,rfl⟩ := fields5 hu
    obtain ⟨g,t,l,bt,et,rfl⟩ := fields5 hv
    rw [List.eq_getElem_of_length_eq_two ws hw]
    rfl
  split
  · rename_i h
    obtain ⟨rfl,hw,rfl,hu,rfl,hv⟩ := h
    obtain ⟨f,s,k,bs,es,rfl⟩ := fields5 hu
    obtain ⟨g,t,l,bt,et,rfl⟩ := fields5 hv
    rw [List.eq_getElem_of_length_eq_two ws hw]
    rfl
  split
  · rename_i h
    obtain ⟨rfl,hw,rfl,hu,rfl,hv⟩ := h
    obtain ⟨w,rfl⟩ := List.length_eq_one_iff.mp hw
    obtain ⟨s,t,q,a,rfl⟩ := fields4 hu
    obtain ⟨u,v,r,b,rfl⟩ := fields4 hv
    rfl
  · unfold context
    split <;> simp_all [fits]

theorem nodesPrim : Primrec NumberedWindowFieldAlgorithm.unpackNode := Primrec.encode_iff.mp
  ((GorbowPRProgram.Proof.unaryCorrespondence _).mpr NumberedWindowFieldProgramChecks.exact_TaggedNodePrograms.2)

theorem nextPrim : Primrec (fun p : Node × Frame => next p.1.1 p.1.2 p.2.1 p.2.2.2) := by
  let F := Node × Frame
  let E := (F × Node) × Node
  have s : Primrec (fun p : F => p.2.1) := Primrec.fst.comp Primrec.snd
  have t : Primrec (fun p : F × Node => p.1.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have head : Primrec (fun p : E => p.1.1.1) := Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have body : Primrec (fun p : E => (p.1.2,p.2)) :=
    (Primrec.snd.comp Primrec.fst).pair Primrec.snd
  exact Primrec.option_bind (nodesPrim.comp s) (Primrec.option_bind (nodesPrim.comp t)
    ((compiledPrim.of_eq compare).comp (head.pair body)).to₂).to₂

end LogicLineages.PersistentMarking.NumberedWindowRawContextFramePrograms
