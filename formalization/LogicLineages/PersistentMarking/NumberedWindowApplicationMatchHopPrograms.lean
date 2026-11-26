module

public import LogicLineages.PersistentMarking.NumberedWindowApplicationMatchProgramTargets
import LogicLineages.PersistentMarking.NumberedWindowRawApplicationLiftProgramChecks
import LogicLineages.PersistentMarking.NumberedWindowPositivePathParserPrograms
import LogicLineages.PersistentMarking.NumberedWindowMarkRootProgramProof
import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowApplicationMatchHopPrograms
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowPositivePathAlgorithm (RawEdge ClassHop hopView)
open NumberedWindowFieldAlgorithm (packNode)
open NumberedWindowClassApplicationHop NumberedWindowRawApplicationLift
open NumberedWindowRawApplicationLiftProgramChecks (exact_RawApplicationLiftProgram)
open NumberedWindowMarkRootProgramProof (nodePrim)
open NumberedWindowPositivePathParserPrograms (hopPrim)

abbrev Config := Nat × Nat × Nat
abbrev ScopeInput (Scope : Type) := Scope × Config

private theorem rawPrim : Primrec (fun p : Config × RawEdge =>
    lift p.1.1 p.1.2.1 p.1.2.2 p.2.1 p.2.2.1 p.2.2.2) := by
  let P := Config × RawEdge
  have d : Primrec (fun p : P => p.1.1) := Primrec.fst.comp Primrec.fst
  have c : Primrec (fun p : P => p.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have a : Primrec (fun p : P => p.1.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have q : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
  have w : Primrec (fun p : P => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have r : Primrec (fun p : P => p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have args := Primrec.vector_cons.comp d (Primrec.vector_cons.comp c
    (Primrec.vector_cons.comp a (Primrec.vector_cons.comp q (Primrec.vector_cons.comp w
      (Primrec.vector_cons.comp r (Primrec.const List.Vector.nil))))))
  obtain ⟨program,h⟩ := exact_RawApplicationLiftProgram
  apply Primrec.encode_iff.mp
  exact ((Proof.primitiveEvaluation 6 program).comp args).of_eq
    (fun p => h p.1.1 p.1.2.1 p.1.2.2 p.2.1 p.2.2.1 p.2.2.2)

private def closeHop {Scope : Type} (least : Scope → Nat → Option Nat)
    (p : Scope × RawEdge) : Option (Nat × Nat × Nat) := do
  let x ← least p.1 p.2.1
  let y ← least p.1 p.2.2.2
  pure (x,y,packNode 2 [y,packNode 1 [p.2.1,p.2.2.2,p.2.2.1]])

private theorem closePrim {Scope : Type} [Primcodable Scope]
    (least : Scope → Nat → Option Nat) (hl : Primrec₂ least) :
    Primrec (closeHop least) := by
  let P := ((Scope × RawEdge) × Nat) × Nat
  have rawRow : Primrec (fun p : P => p.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have rawQ := Primrec.fst.comp rawRow
  have rawR := Primrec.snd.comp (Primrec.snd.comp rawRow)
  have rawW := Primrec.fst.comp (Primrec.snd.comp rawRow)
  have newQ : Primrec (fun p : P => p.1.2) := Primrec.snd.comp Primrec.fst
  have newR : Primrec (fun p : P => p.2) := Primrec.snd
  have edge := nodePrim.comp (Primrec.const 1) (Primrec.list_cons.comp rawQ
    (Primrec.list_cons.comp rawR (Primrec.list_cons.comp rawW (Primrec.const []))))
  have hop := nodePrim.comp (Primrec.const 2)
    (Primrec.list_cons.comp newR (Primrec.list_cons.comp edge (Primrec.const [])))
  have packed := Primrec.option_some.comp (newQ.pair (newR.pair hop))
  have scope : Primrec (Prod.fst : Scope × RawEdge → Scope) := Primrec.fst
  have row : Primrec (Prod.snd : Scope × RawEdge → RawEdge) := Primrec.snd
  have x := hl.comp scope (Primrec.fst.comp row)
  have y := hl.comp scope (Primrec.snd.comp (Primrec.snd.comp row))
  have afterSource := Primrec.option_bind
    (y.comp (Primrec.fst : Primrec (Prod.fst : (Scope × RawEdge) × Nat → Scope × RawEdge))) packed.to₂
  exact Primrec.option_bind x afterSource.to₂

/-- The same hop transform allows the least calculation to depend on
parameters computed from the input address. -/
theorem liftHopScopedPrim {Scope : Type} [Primcodable Scope]
    (least : Scope → Nat → Option Nat) (hl : Primrec₂ least) :
    Primrec (fun p : ScopeInput Scope × Nat =>
      liftHop (least p.1.1) p.1.2.1 p.1.2.2.1 p.1.2.2.2 p.2) := by
  let P := ScopeInput Scope × Nat
  let Q := P × ClassHop
  have scope : Primrec (fun p : Q => p.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have config : Primrec (fun p : Q => p.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have row : Primrec (fun p : Q => p.2.2) := Primrec.snd.comp Primrec.snd
  have onHop := (closePrim least hl).comp (scope.pair (rawPrim.comp (config.pair row)))
  apply (Primrec.option_bind (hopPrim.comp (Primrec.snd : Primrec (Prod.snd : P → Nat)))
    onHop.to₂).of_eq
  intro i
  unfold liftHop
  cases hopView i.2 with
  | none => rfl
  | some hop =>
    rcases hop with ⟨target,q,w,r⟩
    rfl

end LogicLineages.PersistentMarking.NumberedWindowApplicationMatchHopPrograms
