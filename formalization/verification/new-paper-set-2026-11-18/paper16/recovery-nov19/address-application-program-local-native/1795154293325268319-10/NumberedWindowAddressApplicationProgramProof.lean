module

public import LogicLineages.PersistentMarking.NumberedWindowAddressApplicationProgramTargets
import LogicLineages.PersistentMarking.NumberedWindowScalarProgramProof
import LogicLineages.PersistentMarking.NumberedWindowAddressProgramProof
import LogicLineages.PersistentMarking.NumberedWindowFieldProgramChecks
import LogicLineages.PersistentMarking.NumberedWindowMarkRootProgramProof
import LogicLineages.PersistentMarking.NumberedWindowPositivePathParserPrograms
import LogicLineages.PersistentMarking.NumberedWindowSyntaxShapePrograms
import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowAddressApplicationProgramProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowAddressApplication NumberedWindowAddressApplicationProgramTargets
open NumberedWindowAddressAlgorithm (Address addressView)
open NumberedWindowAddressProgramProof (addressPrim)
open NumberedWindowScalarAlgorithm (Settings canonical)
open NumberedWindowScalarProgramProof (admittedPrim leastPrim)
open NumberedWindowMarkRootProgramProof (nodePrim)
open NumberedWindowPositivePathParserPrograms (equalPrim)

private theorem arrowPrim : Primrec arrowView := by
  apply (Primrec.nat_casesOn₁ none NumberedWindowSyntaxShapePrograms.pairs).of_eq
  intro n
  cases n <;> rfl

private theorem packPrim : Primrec NumberedWindowFieldAlgorithm.pack := by
  obtain ⟨p,h⟩ := NumberedWindowFieldProgramChecks.exact_OrderedFieldPrograms.1
  apply ((Proof.primitiveEvaluation 1 p).comp
    (Primrec.vector_cons.comp Primrec.encode (Primrec.const List.Vector.nil))).of_eq
  exact h

private theorem canonicalPrim (s : Settings) : Primrec (canonical s) :=
  Primrec.and.comp (admittedPrim s)
    (equalPrim.comp (leastPrim s) (Primrec.option_some.comp (Primrec.snd.comp Primrec.snd)))

private theorem applyPrim (s : Settings) :
    Primrec₂ (applyAddresses s) := by
  let P := Address × Address
  let E := P × Nat × Nat
  have q : Primrec (fun p : E => p.1.1) := Primrec.fst.comp Primrec.fst
  have u : Primrec (fun p : E => p.1.2) := Primrec.snd.comp Primrec.fst
  have ctx := Primrec.fst.comp q
  have dom : Primrec (fun p : E => p.2.1) := Primrec.fst.comp Primrec.snd
  have cod : Primrec (fun p : E => p.2.2) := Primrec.snd.comp Primrec.snd
  have qLeast := Primrec.snd.comp (Primrec.snd.comp q)
  have uLeast := Primrec.snd.comp (Primrec.snd.comp u)
  have same := equalPrim.comp ctx (Primrec.fst.comp u)
  have typed := equalPrim.comp dom (Primrec.fst.comp (Primrec.snd.comp u))
  have guard := Primrec.and.comp
    (Primrec.and.comp (Primrec.and.comp ((canonicalPrim s).comp q) ((canonicalPrim s).comp u)) same) typed
  have term := nodePrim.comp (Primrec.const 6) (Primrec.list_cons.comp dom
    (Primrec.list_cons.comp cod (Primrec.list_cons.comp qLeast
      (Primrec.list_cons.comp uLeast (Primrec.const [])))))
  have out := (leastPrim s).comp (ctx.pair (cod.pair term))
  have outputAddr : Primrec (fun p : E × Nat => NumberedWindowFieldAlgorithm.packNode 3
      [NumberedWindowFieldAlgorithm.pack p.1.1.1.1,p.1.2.2,p.2]) :=
    nodePrim.comp (Primrec.const 3) (Primrec.list_cons.comp (packPrim.comp (ctx.comp Primrec.fst))
      (Primrec.list_cons.comp (cod.comp Primrec.fst) (Primrec.list_cons.comp Primrec.snd (Primrec.const []))))
  have committed := Primrec.ite (Primrec.eq.comp guard (Primrec.const true))
    (Primrec.option_map out outputAddr.to₂) (Primrec.const none)
  have arrow : Primrec (fun p : P => arrowView p.1.2.1) :=
    arrowPrim.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
  apply (Primrec.option_bind arrow committed.to₂).to₂.of_eq
  intro q u
  cases h : arrowView q.2.1 with
  | none => simp [applyAddresses,h]
  | some a =>
    rcases a with ⟨dom,cod⟩
    simp [applyAddresses,h]

theorem applicationPrim (s : Settings) : Primrec₂ (application s) := by
  let P := Nat × Nat
  let Q := P × Address
  have arg : Primrec (fun p : Q => addressView p.1.2) :=
    addressPrim.comp (Primrec.snd.comp Primrec.fst)
  have applyArgs : Primrec₂ (fun (a : Q) u => applyAddresses s a.2 u) :=
    (applyPrim s).comp (Primrec.snd.comp Primrec.fst) Primrec.snd |>.to₂
  exact Primrec.option_bind (addressPrim.comp Primrec.fst) (Primrec.option_bind arg applyArgs).to₂

theorem graphPrim (s : Settings) : Primrec (fun p : Nat × Nat × Nat => graph s p.1 p.2.1 p.2.2) :=
  equalPrim.comp ((applicationPrim s).comp Primrec.fst (Primrec.fst.comp Primrec.snd))
    (Primrec.option_some.comp (Primrec.snd.comp Primrec.snd))

private theorem indicator (b : Bool) : (if b then 1 else 0) = b.toNat := by cases b <;> rfl

theorem programs : ApplicationPrograms := by
  intro s
  constructor
  · have q : Primrec (fun v : List.Vector Nat 2 => v.head) := Primrec.vector_head
    have u := Primrec.vector_head.comp (Primrec.vector_tail : Primrec (fun v : List.Vector Nat 2 => v.tail))
    obtain ⟨p,h⟩ := Proof.allPrimitiveFunctions 2 _
      (Primrec.encode.comp ((applicationPrim s).comp q u))
    exact ⟨p,fun q u => h (q ::ᵥ u ::ᵥ nil)⟩
  · have q : Primrec (fun v : List.Vector Nat 3 => v.head) := Primrec.vector_head
    have u := Primrec.vector_head.comp (Primrec.vector_tail : Primrec (fun v : List.Vector Nat 3 => v.tail))
    have r := Primrec.vector_head.comp (Primrec.vector_tail.comp
      (Primrec.vector_tail : Primrec (fun v : List.Vector Nat 3 => v.tail)))
    have gt := (graphPrim s).comp (q.pair (u.pair r))
    obtain ⟨p,h⟩ := Proof.allPrimitiveFunctions 3 _
      (Primrec.ite (Primrec.eq.comp gt (Primrec.const true)) (Primrec.const (1 : Nat)) (Primrec.const 0))
    exact ⟨p,fun q u r => (h (q ::ᵥ u ::ᵥ r ::ᵥ nil)).trans (indicator _)⟩

end LogicLineages.PersistentMarking.NumberedWindowAddressApplicationProgramProof
