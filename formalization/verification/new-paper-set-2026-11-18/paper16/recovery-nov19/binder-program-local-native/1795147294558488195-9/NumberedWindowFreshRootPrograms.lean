module
public import LogicLineages.PersistentMarking.NumberedWindowBinderRootProgramTargets
import LogicLineages.PersistentMarking.NumberedWindowShiftProgramProof
import LogicLineages.PersistentMarking.NumberedWindowPositivePathParserPrograms
import LogicLineages.PersistentMarking.NumberedWindowMarkRootProgramProof
import LogicLineages.PersistentMarking.NumberedWindowSyntaxShapePrograms
import LogicLineages.PersistentMarking.NumberedWindowFieldProgramChecks
import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof
public section
namespace LogicLineages.PersistentMarking.NumberedWindowFreshRootPrograms
open NumberedWindowBinderRootAlgorithm
open NumberedWindowMarkRootProgramProof (nodePrim guardPrim readPrim)
open NumberedWindowSyntaxShapePrograms (pairs anyOption)
open NumberedWindowPositivePathParserPrograms (fieldsPrim equalPrim)
open LogicLineages.ComputabilityKnowledge

private theorem packPrim : Primrec NumberedWindowFieldAlgorithm.pack := by
  obtain ⟨p,ev⟩ := NumberedWindowFieldProgramChecks.exact_OrderedFieldPrograms.1
  exact ((GorbowPRProgram.Proof.primitiveEvaluation 1 p).comp
    (Primrec.vector_cons.comp Primrec.encode (Primrec.const List.Vector.nil))).of_eq ev

private theorem appendFresh {α} [Primcodable α] {σ : α → Nat} {xs : α → List Nat}
    (dom : Primrec σ) (list : Primrec xs) : Primrec (fun x =>
      NumberedWindowFieldAlgorithm.pack (xs x ++ [NumberedWindowFieldAlgorithm.packNode 1 [σ x,0]])) :=
  packPrim.comp (Primrec.list_append.comp list (Primrec.list_cons.comp
    (nodePrim.comp (Primrec.const 1) (Primrec.list_cons.comp dom (Primrec.const [0]))) (Primrec.const [])))

private theorem freshPrim {α} [Primcodable α] {f σ τ k bs es : α → Nat} (hf : Primrec f)
    (dom : Primrec σ) (cod : Primrec τ) (hk : Primrec k) (hb : Primrec bs) (he : Primrec es) :
    Primrec (fun x => freshBody (f x) (σ x) (τ x) (k x) (bs x) (es x)) := by
  let shiftA (v : α → Nat) (hv : Primrec v) := Primrec.snd.comp
    (NumberedWindowShiftProgramProof.outputPrim.comp ((Primrec.const 1).pair ((Primrec.const 0).pair hv)))
  let P := ((α × Nat) × Nat) × List Nat
  have outer : Primrec (fun x : P => x.1.1.1) := Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have b : Primrec (fun x : P => x.1.1.2) := Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have extended := appendFresh (dom.comp outer) (Primrec.snd : Primrec (Prod.snd : P → _))
  have own := nodePrim.comp (Primrec.const 5) (Primrec.list_cons.comp (hf.comp outer)
    (Primrec.list_cons.comp (cod.comp outer) (Primrec.list_cons.comp (hk.comp outer)
      (Primrec.list_cons.comp b (Primrec.list_cons.comp extended (Primrec.const []))))))
  have lam := nodePrim.comp (Primrec.const 2) (Primrec.list_cons.comp (dom.comp outer)
    (Primrec.list_cons.comp own (Primrec.const [])))
  exact Primrec.option_bind (shiftA bs hb) (Primrec.option_bind ((shiftA es he).comp Primrec.fst)
    (Primrec.option_bind (fieldsPrim.comp Primrec.snd) (Primrec.option_some.comp lam).to₂).to₂).to₂

abbrev Node := Nat × List Nat

theorem fabsPrim : Primrec₂ fabs := by
  let P := (Nat × Nat) × Node
  have tag : Primrec (fun x : P => x.2.1) := Primrec.fst.comp Primrec.snd
  have fs : Primrec (fun x : P => x.2.2) := Primrec.snd.comp Primrec.snd
  have dst : Primrec (fun x : P => x.1.2) := Primrec.snd.comp Primrec.fst
  let v (i : Nat) := (Primrec.list_getD 0).comp fs (Primrec.const i)
  let nz (i : Nat) := Primrec.not.comp (equalPrim.comp (v i) (Primrec.const 0))
  have guard := Primrec.and.comp (Primrec.and.comp (equalPrim.comp tag (Primrec.const 5)) (nz 2)) (nz 1)
  let Q := P × Nat × Nat
  have dom : Primrec (fun x : Q => x.2.1) := Primrec.fst.comp Primrec.snd
  have cod : Primrec (fun x : Q => x.2.2) := Primrec.snd.comp Primrec.snd
  have expected := freshPrim ((v 0).comp Primrec.fst) dom cod
    ((Primrec.pred.comp (v 2)).comp Primrec.fst) ((v 3).comp Primrec.fst) ((v 4).comp Primrec.fst)
  have result := anyOption expected ((equalPrim.comp Primrec.snd ((dst.comp Primrec.fst).comp Primrec.fst)).to₂)
  have predTy := pairs.comp (Primrec.pred.comp (v 1))
  exact guardPrim Primrec.fst Primrec.snd (anyOption (readPrim.comp Primrec.fst)
    (Primrec.and.comp guard (anyOption predTy result.to₂)).to₂)
end LogicLineages.PersistentMarking.NumberedWindowFreshRootPrograms
