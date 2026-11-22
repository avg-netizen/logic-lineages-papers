module
public import LogicLineages.PermittedControl.ActualSignedRouteCartesianTargets
import LogicLineages.PermittedControl.ActualSelectedSignedRoutePacketFoldProof
import LogicLineages.PermittedControl.OriginalMatrixLinearRowFormulaShapeProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualSignedRouteCartesian
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open ActualPreparedSlotAppend (Packet append)
open ActualSelectedSignedRoutePacket (Shape exactRouteAppend)
open ActualBoundedSignedRoutes (PacketHolds)
open OriginalMatrixLinearRowFormula (safeTruth)

theorem exactTupleChoice : ExactTupleChoice := by
  intro rows
  induction rows with
  | nil =>
    intro ps
    constructor
    · intro used
      have eq := List.mem_singleton.mp used
      subst ps
      exact .nil
    · intro hs
      cases hs
      exact List.mem_singleton.mpr rfl
  | cons row rows ih =>
    intro ps
    constructor
    · intro used
      obtain ⟨p,hp,rest⟩ := List.mem_flatMap.mp used
      obtain ⟨tail,ht,rfl⟩ := List.mem_map.mp rest
      exact .cons hp ((ih tail).mp ht)
    · intro hs
      cases hs with
      | cons hp ht =>
        exact List.mem_flatMap.mpr ⟨_,hp,List.mem_map.mpr ⟨_,(ih _).mpr ht,rfl⟩⟩

private theorem baseHolds (f baseline : Nat → Nat) (top z : Nat) :
    PacketHolds f baseline top z (tuplePacket []) :=
  ⟨fun _ => 0,fun j used => False.elim (Nat.not_lt_zero j used),True.intro⟩

theorem exactCartesianPacketEval : ExactCartesianPacketEval := by
  intro f baseline top z rows
  induction rows with
  | nil =>
    intro _
    refine ⟨?_,?_⟩
    · intro ps used
      have eq := List.mem_singleton.mp used
      subst ps
      exact safeTruth []
    · exact ⟨fun _ row used => False.elim (List.not_mem_nil used),
        fun _ => ⟨[],List.mem_singleton.mpr rfl,baseHolds f baseline top z⟩⟩
  | cons row rows ih =>
    intro shape
    have tail := ih (fun family used => shape family (List.mem_cons_of_mem _ used))
    have decomp (ps : List Packet) (used : ps ∈ choices (row::rows)) :
        ∃ p ∈ row, ∃ rest ∈ choices rows, ps = p::rest := by
      obtain ⟨p,hp,member⟩ := List.mem_flatMap.mp used
      obtain ⟨rest,ht,eq⟩ := List.mem_map.mp member
      exact ⟨p,hp,rest,ht,eq.symm⟩
    have ready (p : Packet) (hp : p ∈ row) (rest : List Packet) (hr : rest ∈ choices rows) :=
      exactRouteAppend f baseline top z p (tuplePacket rest) (shape row List.mem_cons_self p hp) (tail.1 rest hr)
    refine ⟨?_,?_⟩
    · intro ps used
      obtain ⟨p,hp,rest,hr,rfl⟩ := decomp ps used
      exact (ready p hp rest hr).1
    constructor
    · rintro ⟨ps,used,passes⟩
      obtain ⟨p,hp,rest,hr,rfl⟩ := decomp ps used
      obtain ⟨head,others⟩ := (ready p hp rest hr).2.mp passes
      have live := tail.2.mp ⟨rest,hr,others⟩
      intro family member
      rcases List.mem_cons.mp member with same | lower
      · subst family
        exact ⟨p,hp,head⟩
      · exact live family lower
    · intro live
      obtain ⟨p,hp,head⟩ := live row List.mem_cons_self
      obtain ⟨rest,hr,others⟩ := tail.2.mpr (fun family used => live family (List.mem_cons_of_mem _ used))
      refine ⟨p::rest,List.mem_flatMap.mpr ⟨p,hp,List.mem_map.mpr ⟨rest,hr,rfl⟩⟩,?_⟩
      exact (ready p hp rest hr).2.mpr ⟨head,others⟩

end LogicLineages.PermittedControl.ActualSignedRouteCartesian
