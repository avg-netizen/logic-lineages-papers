module

public import LogicLineages.PersistentMarking.NumberedWindowApplicationMatchHopPrograms
import LogicLineages.PersistentMarking.NumberedWindowFieldProgramChecks
import LogicLineages.PersistentMarking.NumberedWindowPositivePathParserPrograms
import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowApplicationMatchPathPrograms
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowClassApplicationPath
open NumberedWindowApplicationMatchHopPrograms (ScopeInput liftHopScopedPrim)
open NumberedWindowFieldAlgorithm (pack unpack)
open NumberedWindowPositivePathParserPrograms (fieldsPrim)

abbrev ScopedPathInput (Scope : Type) := ScopeInput Scope × Nat × Nat

private theorem packPrim : Primrec pack := by
  obtain ⟨p,h⟩ := NumberedWindowFieldProgramChecks.exact_OrderedFieldPrograms.1
  apply ((Proof.primitiveEvaluation 1 p).comp
    (Primrec.vector_cons.comp Primrec.encode (Primrec.const List.Vector.nil))).of_eq
  exact h

private theorem advancePrim {Scope : Type} [Primcodable Scope]
    (least : Scope → Nat → Option Nat) (hl : Primrec₂ least) :
    Primrec (fun p : ScopeInput Scope × Option Accumulator × Nat =>
      advance (least p.1.1) p.1.2.1 p.1.2.2.1 p.1.2.2.2 p.2.1 p.2.2) := by
  let P := ScopeInput Scope × Option Accumulator × Nat
  let Q := P × Accumulator
  let R := Q × Nat × Nat × Nat
  have config : Primrec (fun p : Q => p.1.1) := Primrec.fst.comp Primrec.fst
  have oldHop : Primrec (fun p : Q => p.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have src : Primrec (fun p : R => p.2.1) := Primrec.fst.comp Primrec.snd
  have dst : Primrec (fun p : R => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have newHop : Primrec (fun p : R => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have cur : Primrec (fun p : R => p.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have done : Primrec (fun p : R => p.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have check : Primrec (fun p : R => if p.2.1 == p.1.2.1 then
      some (p.2.2.1,p.2.2.2 :: p.1.2.2) else none) :=
    Primrec.ite (Primrec.eq.comp (NumberedWindowPositivePathParserPrograms.equalPrim.comp src cur)
      (Primrec.const true))
      (Primrec.option_some.comp (dst.pair (Primrec.list_cons.comp newHop done))) (Primrec.const none)
  have updated := Primrec.option_bind ((liftHopScopedPrim least hl).comp (config.pair oldHop)) check.to₂
  apply (Primrec.option_bind (Primrec.fst.comp (Primrec.snd : Primrec (Prod.snd : P → _)))
    updated.to₂).of_eq
  intro p
  cases state : p.2.1 with
  | none => simp [advance]
  | some active =>
    rcases active with ⟨cur,done⟩
    cases h : NumberedWindowClassApplicationHop.liftHop (least p.1.1)
        p.1.2.1 p.1.2.2.1 p.1.2.2.2 p.2.2 with
    | none => simp [advance,h]
    | some hop =>
      rcases hop with ⟨src,dst,code⟩
      simp [advance,h]

/-- The original fold works uniformly with least at the input context and result fiber. -/
theorem liftPathScopedPrim {Scope : Type} [Primcodable Scope]
    (least : Scope → Nat → Option Nat) (hl : Primrec₂ least) :
    Primrec (fun p : ScopedPathInput Scope =>
      liftPath (least p.1.1) p.1.2.1 p.1.2.2.1 p.1.2.2.2 p.2.1 p.2.2) := by
  let Input := ScopedPathInput Scope
  let Data := Input × List Nat
  have source : Primrec (fun p : Data => p.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have config : Primrec (fun p : Data × Option Accumulator × Nat => p.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hops : Primrec (Prod.snd : Data → List Nat) := Primrec.snd
  have folded := Primrec.list_foldl hops
    (Primrec.option_some.comp (source.pair (Primrec.const ([] : List Nat))))
    ((advancePrim least hl).comp (config.pair Primrec.snd)).to₂
  have nonempty : Primrec (fun p : Data => p.2.isEmpty) :=
    ((Primrec.eq.comp hops (Primrec.const ([] : List Nat))).decide).of_eq
      (fun p => by cases p.2 <;> simp)
  have finish : Primrec (fun p : Accumulator => (p.1,pack p.2.reverse)) :=
    Primrec.fst.pair (packPrim.comp (Primrec.list_reverse.comp Primrec.snd))
  have committed := Primrec.ite (Primrec.eq.comp nonempty (Primrec.const true))
    (Primrec.const none) (Primrec.option_map₁ finish |>.comp folded)
  apply (Primrec.option_bind (fieldsPrim.comp (Primrec.snd.comp
    (Primrec.snd : Primrec (Prod.snd : Input → Nat × Nat)))) committed.to₂).of_eq
  intro p
  unfold liftPath
  cases unpack p.2.2 with
  | none => rfl
  | some hops =>
    change (if hops.isEmpty then none else
      (hops.foldl (advance (least p.1.1) p.1.2.1 p.1.2.2.1 p.1.2.2.2) (some (p.2.1,[]))).map
        (fun out => (out.1,pack out.2.reverse))) = _
    simp only [Option.bind_eq_bind,Option.bind_some]
    by_cases empty : hops.isEmpty = true
    · simp only [empty,if_true]
    · simp only [empty,if_false]
      cases h : hops.foldl (advance (least p.1.1) p.1.2.1 p.1.2.2.1 p.1.2.2.2) (some (p.2.1,[])) with
      | none => rfl
      | some out => cases out; rfl

end LogicLineages.PersistentMarking.NumberedWindowApplicationMatchPathPrograms
