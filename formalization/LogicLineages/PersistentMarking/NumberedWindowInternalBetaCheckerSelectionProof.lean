module
public import LogicLineages.PersistentMarking.NumberedWindowInternalBetaCheckerFitProof
import LogicLineages.PersistentMarking.NumberedWindowMarkRootProgramProof
import LogicLineages.PersistentMarking.NumberedWindowPositivePathParserPrograms
import LogicLineages.PersistentMarking.NumberedWindowSyntaxShapePrograms
import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalBetaCheckerSelectionProof

open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowMarkRootProgramProof (readPrim guardPrim)
open NumberedWindowPositivePathParserPrograms (equalPrim)
open NumberedWindowSyntaxShapePrograms (anyOption)
open NumberedWindowInternalBetaCheckerFitProof
open NumberedWindowInternalBetaSub

private abbrev Node := Nat × List Nat
private abbrev Fields := Node × Node

private theorem slot (i : Nat) : Primrec (fun p : Node => p.2.getD i 0) :=
  (Primrec.list_getD 0).comp Primrec.snd (Primrec.const i)

private theorem fieldsPrim : Primrec fields := by
  have attached : Primrec (fun p : Node =>
      (NumberedWindowFieldAlgorithm.unpackNode (p.2.getD 2 0)).map (fun f => (p,f))) :=
    Primrec.option_map (readPrim.comp (slot 2))
      (Primrec.pair Primrec.fst Primrec.snd).to₂
  apply ((Primrec.option_bind₁ attached).comp readPrim).of_eq
  intro src
  unfold fields
  cases NumberedWindowFieldAlgorithm.unpackNode src with
  | none => rfl
  | some p =>
      change
        (NumberedWindowFieldAlgorithm.unpackNode (p.2.getD 2 0)).map (fun f => (p,f)) =
        (NumberedWindowFieldAlgorithm.unpackNode (p.2.getD 2 0)).bind (fun f => some (p,f))
      cases NumberedWindowFieldAlgorithm.unpackNode (p.2.getD 2 0) <;> rfl

private theorem binderPrim : Primrec (fun f : Fields => binderBits f.1 f.2) := by
  have leftTag : Primrec (fun f : Fields => f.1.1) := Primrec.fst.comp Primrec.fst
  have rightTag : Primrec (fun f : Fields => f.2.1) := Primrec.fst.comp Primrec.snd
  have leftDom : Primrec (fun f : Fields => f.1.2.getD 0 0) := (slot 0).comp Primrec.fst
  have rightDom : Primrec (fun f : Fields => f.2.2.getD 0 0) := (slot 0).comp Primrec.snd
  exact Primrec.and.comp (Primrec.and.comp
    (equalPrim.comp leftTag (Primrec.const 6)) (equalPrim.comp rightTag (Primrec.const 2)))
    (equalPrim.comp leftDom rightDom)

private theorem coordinate {f : Fields → Nat} (hf : Primrec f) :
    Primrec (fun src => ((fields src).map f).getD 0) :=
  Primrec.option_getD.comp ((Primrec.option_map₁ hf).comp fieldsPrim) (Primrec.const 0)

theorem selected : ∃ guard arg body : Program 2,
    (∀ src dst, run2 guard src dst = guardSpec src dst) ∧
    (∀ src dst, run2 arg src dst = argSpec src) ∧
    (∀ src dst, run2 body src dst = bodySpec src) := by
  let V := List.Vector Nat 2
  have src : Primrec (fun v : V => v.head) := Primrec.vector_head
  have dst : Primrec (fun v : V => v.tail.head) := Primrec.vector_head.comp Primrec.vector_tail
  have test := anyOption fieldsPrim (binderPrim.comp (Primrec.snd : Primrec (fun p : Nat × Fields => p.2))).to₂
  have guarded := guardPrim src dst (test.comp src)
  have guard : Primrec (fun v : V => guardSpec v.head v.tail.head) := by
    apply (Primrec.cond guarded (Primrec.const (1 : Nat)) (Primrec.const 0)).of_eq
    intro v
    unfold guardSpec
    cases NumberedWindowMarkRootAlgorithm.guarded v.head v.tail.head
      ((fields v.head).any fun f => binderBits f.1 f.2) <;> rfl
  have arg : Primrec argSpec := coordinate ((slot 3).comp Primrec.fst)
  have body : Primrec bodySpec := coordinate ((slot 1).comp Primrec.snd)
  obtain ⟨g,hg⟩ := Proof.allPrimitiveFunctions 2 _ guard
  obtain ⟨a,ha⟩ := Proof.allPrimitiveFunctions 2 _ (arg.comp src)
  obtain ⟨b,hb⟩ := Proof.allPrimitiveFunctions 2 _ (body.comp src)
  exact ⟨g,a,b,fun x y => hg (x ::ᵥ y ::ᵥ nil),fun x y => ha (x ::ᵥ y ::ᵥ nil),
    fun x y => hb (x ::ᵥ y ::ᵥ nil)⟩

#print axioms selected
end LogicLineages.PersistentMarking.NumberedWindowInternalBetaCheckerSelectionProof
