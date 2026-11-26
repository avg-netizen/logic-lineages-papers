module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickTargets
import LogicLineages.PersistentMarking.NumberedWindowRawContextFramePrograms
import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickFallbackChecks
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open NumberedWindowRawContextAlgorithm (Frame)
open NumberedWindowRawContextFramePrograms (Node nodesPrim nextPrim)
open NumberedWindowInternalSparseRawFunctionFrame (encodeFrame)
open NumberedWindowInternalSparseRawTick (fallbackValue)
open NumberedWindowInternalSparseRawTickTargets
open NumberedWindowPairAlgorithm (pair)

private theorem coord (i : Fin 3) :
    Primrec (fun v : List.Vector Nat 3 => v.get i) :=
  Primrec.vector_get.comp Primrec.id (Primrec.const i)

private theorem poly : Primrec (fun p : Nat × Nat => pair p.1 p.2) := by
  have s := Primrec.nat_add.comp Primrec.fst Primrec.snd
  exact Primrec.nat_add.comp (Primrec.nat_mul.comp s s) Primrec.fst

private theorem push {α : Type} {f g : α → Nat} [Primcodable α]
    (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => pair (f a) (g a) + 1) :=
  Primrec.succ.comp (poly.comp (hf.pair hg))

private theorem scratch : Primrec (fun f : Frame => encodeFrame (some f)) := by
  have a : Primrec (fun f : Frame => f.1) := Primrec.fst
  have b : Primrec (fun f : Frame => f.2.1) := Primrec.fst.comp Primrec.snd
  have c : Primrec (fun f : Frame => f.2.2) := Primrec.snd.comp Primrec.snd
  exact Primrec.succ.comp (push a (push b (push c (Primrec.const 0))))

private theorem decoded :
    Primrec (fun v : List.Vector Nat 3 => fallbackValue (v.get 0) (v.get 1) (v.get 2)) := by
  let V := List.Vector Nat 3
  let N := V × Node
  have q : Primrec (fun p : N => p.1.get 0) := (coord 0).comp Primrec.fst
  have w : Primrec (fun p : N => p.1.get 1) := (coord 1).comp Primrec.fst
  have r : Primrec (fun p : N => p.1.get 2) := (coord 2).comp Primrec.fst
  have move : Primrec (fun p : N => (p.2,(p.1.get 0,p.1.get 1,p.1.get 2))) :=
    Primrec.snd.pair (q.pair (w.pair r))
  exact Primrec.option_bind (nodesPrim.comp (coord 1)) (nextPrim.comp move).to₂

theorem exact_ConcreteFallback : ExactConcreteFallback := by
  let V := List.Vector Nat 3
  let f (v : V) := encodeFrame (fallbackValue (v.get 0) (v.get 1) (v.get 2))
  have store : Primrec (fun p : V × Frame => encodeFrame (some p.2)) :=
    scratch.comp Primrec.snd
  have h : Primrec f := (Primrec.option_getD.comp
    (Primrec.option_map decoded store.to₂) (Primrec.const 0)).of_eq (fun v => by
      dsimp only [f]
      cases fallbackValue (v.get 0) (v.get 1) (v.get 2) <;> rfl)
  obtain ⟨p,hp⟩ := GorbowPRProgram.Proof.allPrimitiveFunctions 3 f h
  exact ⟨p,fun q w r => hp (q ::ᵥ w ::ᵥ r ::ᵥ nil)⟩

#print axioms exact_ConcreteFallback
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickFallbackChecks
