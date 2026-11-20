module

public import LogicLineages.PersistentMarking.NumberedWindowOwnerAlgorithm
import LogicLineages.PersistentMarking.NumberedWindowMarkRootProgramProof
import LogicLineages.PersistentMarking.NumberedWindowHeadDeclarationPrograms
import LogicLineages.PersistentMarking.NumberedWindowFieldProgramChecks
import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowOwnerPrograms
open NumberedWindowOwnerAlgorithm NumberedWindowMarkRootProgramProof (nodePrim)
open NumberedWindowHeadDeclarationPrograms (arrowPrim)
open LogicLineages.ComputabilityKnowledge

theorem ownerPrim {α} [Primcodable α] {f k b e t : α → Nat}
    (hf : Primrec f) (hk : Primrec k) (hb : Primrec b) (he : Primrec e) (ht : Primrec t) :
    Primrec (fun x => owner (f x) (k x) (b x) (e x) (t x)) :=
  nodePrim.comp (Primrec.const 5) (Primrec.list_cons.comp hf (Primrec.list_cons.comp ht
    (Primrec.list_cons.comp hk (Primrec.list_cons.comp hb (Primrec.list_cons.comp he (Primrec.const []))))))

theorem copiesPrim {α} [Primcodable α] {f k b e : α → Nat} {ts : α → List Nat}
    (hf : Primrec f) (hk : Primrec k) (hb : Primrec b) (he : Primrec e) (ht : Primrec ts) :
    Primrec (fun x => copies (f x) (k x) (b x) (e x) (ts x)) := by
  obtain ⟨p,ev⟩ := NumberedWindowFieldProgramChecks.exact_OrderedFieldPrograms.1
  have pack : Primrec NumberedWindowFieldAlgorithm.pack :=
    ((GorbowPRProgram.Proof.primitiveEvaluation 1 p).comp
      (Primrec.vector_cons.comp Primrec.encode (Primrec.const List.Vector.nil))).of_eq ev
  exact pack.comp (Primrec.list_map ht (ownerPrim (hf.comp Primrec.fst) (hk.comp Primrec.fst)
    (hb.comp Primrec.fst) (he.comp Primrec.fst) Primrec.snd).to₂)

theorem planPrim : Primrec₂ plan := by
  let P := (Nat × List Nat) × Nat × Nat × List (Nat × Nat)
  have dom : Primrec (fun x : P => x.2.1) := Primrec.fst.comp Primrec.snd
  have rest : Primrec (fun x : P => x.2.2) := Primrec.snd.comp Primrec.snd
  have cod := Primrec.fst.comp rest
  exact Primrec.list_foldr Primrec.snd (Primrec.fst.pair (Primrec.const []))
    (((arrowPrim.comp dom cod).pair (Primrec.list_cons.comp (dom.pair cod) (Primrec.snd.comp rest))).to₂)

theorem applyPrim {α} [Primcodable α] {f k b e q : α → Nat} {steps : α → List (Nat × Nat)}
    (hf : Primrec f) (hk : Primrec k) (hb : Primrec b) (he : Primrec e) (hq : Primrec q)
    (hs : Primrec steps) : Primrec (fun x => applyCopies (f x) (k x) (b x) (e x) (q x) (steps x)) := by
  let P := α × Nat × Nat × Nat
  have current : Primrec (fun x : P => x.2.1) := Primrec.fst.comp Primrec.snd
  have slot : Primrec (fun x : P => x.2.2) := Primrec.snd.comp Primrec.snd
  have dom := Primrec.fst.comp slot
  have arg := ownerPrim (hf.comp Primrec.fst) (hk.comp Primrec.fst) (hb.comp Primrec.fst)
    (he.comp Primrec.fst) dom
  exact Primrec.list_foldl hs hq ((nodePrim.comp (Primrec.const 6)
    (Primrec.list_cons.comp dom (Primrec.list_cons.comp (Primrec.snd.comp slot)
      (Primrec.list_cons.comp current (Primrec.list_cons.comp arg (Primrec.const [])))))).to₂)
end LogicLineages.PersistentMarking.NumberedWindowOwnerPrograms
