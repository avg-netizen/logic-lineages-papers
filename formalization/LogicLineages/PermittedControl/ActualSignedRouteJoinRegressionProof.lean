module
public import LogicLineages.PermittedControl.ActualSignedRouteJoinRegressionTargets
import LogicLineages.PermittedControl.ActualSignedRouteCartesianChoiceProof
import LogicLineages.PermittedControl.ActualSelectedSignedRouteProjectionChosenProof
import LogicLineages.PermittedControl.ActualSymbolicPredecessorProjectionProof
import LogicLineages.PermittedControl.ActualGreatestRouteResidualTableProof
import LogicLineages.PermittedControl.ActualGreatestRouteResidualDecodeProof
import LogicLineages.PermittedControl.ActualGreatestRouteResidualProof
import LogicLineages.PermittedControl.OriginalMatrixLinearRowFormulaShapeProof

public section
namespace LogicLineages.PermittedControl.ActualSignedRouteJoinRegression
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open PreparedProjection
open ActualPreparedSlotAppend (Packet)
open ActualSelectedSignedRoutePacket (Shape)
open ActualBoundedSignedRoutes (PacketHolds)
open ActualSignedRouteCartesian (choices tuplePacket exactTupleChoice exactCartesianPacketEval)
open ActualSelectedSignedRouteProjection (project LowerHolds exactChosenRouteProjection)
open ActualSymbolicPredecessorProjection
  (prepend exactSymbolicPredecessorAppend exactSymbolicPredecessorProjection)
open OriginalRankedLiteralClauseHigh (rankedPredecessor)
open ActualGreatestRouteResidual
  (lowerFamily LowerMatrix StrictLower Residual keep decodeRoute keepMember
    exactDecodedActualResidual exactActualLowerRouteFamily)
open OriginalMatrixLinearRowFormula (safeAtom safeAnd)

theorem pinnedEval (ops : List LowerOperand) (c : Nat) (ν : Nat → Nat) :
    (pinned ops c).2.eval ν ↔ ν 0 = c := by
  change (0 ≤ -(c : Int) + (1 * (ν 0 : Int) + 0)) ∧ (0 ≤ (c : Int) + (-1 * (ν 0 : Int) + 0)) ↔ _
  have e₁ : (1 : Int) * (ν 0 : Int) = (ν 0 : Int) := one_mul _
  have e₂ : (-1 : Int) * (ν 0 : Int) = -(ν 0 : Int) := neg_one_mul _
  rw [e₁,e₂]
  omega

theorem pinnedShape (ops : List LowerOperand) (c : Nat) : Shape (pinned ops c) := by
  change PreparedInput ops (.conjunction (.atom (.nonnegative (-(c : Int),[(1,.variable 0)])))
    (.atom (.nonnegative ((c : Int),[(-1,.variable 0)]))))
  refine safeAnd _ _ _ (safeAtom _ _ ?_ ?_) (safeAtom _ _ ?_ ?_)
  · intro t used
    have eq := List.mem_singleton.mp used
    subst t
    exact ⟨0,rfl⟩
  · intro n used
    change n ∈ [0] at used
    have eq := List.mem_singleton.mp used
    subst n
    exact Nat.zero_le _
  · intro t used
    have eq := List.mem_singleton.mp used
    subst t
    exact ⟨0,rfl⟩
  · intro n used
    change n ∈ [0] at used
    have eq := List.mem_singleton.mp used
    subst n
    exact Nat.zero_le _

theorem exactPinnedPacket : ExactPinnedPacket := by
  intro f baseline top z c ops
  refine ⟨pinnedShape ops c,?_⟩
  have value (ν : Nat → Nat) : (pinned ops c).2.eval (Function.update ν 0 z) ↔ z = c := by
    rw [pinnedEval,Function.update_self]
  constructor
  · rintro ⟨ν,tied,passes⟩
    exact ⟨(value ν).mp passes,ν,tied⟩
  · rintro ⟨eq,ν,tied⟩
    exact ⟨ν,tied,(value ν).mpr eq⟩

private theorem rowsShape (ops₁ ops₂ : List LowerOperand) (C : Nat) :
    ∀ row ∈ [[pinned ops₁ C],[pinned ops₂ (C+1)]], ∀ p ∈ row, Shape p := by
  intro row used p member
  rcases List.mem_cons.mp used with first | rest
  · subst first
    rw [List.mem_singleton.mp member]
    exact pinnedShape _ _
  · rw [List.mem_singleton.mp rest] at member
    rw [List.mem_singleton.mp member]
    exact pinnedShape _ _

private theorem pairChoice (a b : Packet) : [a,b] ∈ choices [[a],[b]] :=
  (exactTupleChoice [[a],[b]] [a,b]).mpr
    (.cons (List.mem_singleton.mpr rfl) (.cons (List.mem_singleton.mpr rfl) .nil))

theorem joinedShape (ops₁ ops₂ : List LowerOperand) (C : Nat) :
    Shape (tuplePacket [pinned ops₁ C,pinned ops₂ (C+1)]) :=
  (exactCartesianPacketEval (fun _ => 0) (fun _ => 0) 0 0 _ (rowsShape ops₁ ops₂ C)).1 _
    (pairChoice _ _)

private theorem noShared (f baseline : Nat → Nat) (top C : Nat) (ops₁ ops₂ : List LowerOperand)
    (z : Nat) :
    ¬ ∃ positions ∈ choices [[pinned ops₁ C],[pinned ops₂ (C+1)]],
        PacketHolds f baseline top z (tuplePacket positions) := by
  intro live
  have each := (exactCartesianPacketEval f baseline top z _ (rowsShape ops₁ ops₂ C)).2.mp live
  obtain ⟨p,hp,h₁⟩ := each [pinned ops₁ C] List.mem_cons_self
  obtain ⟨q,hq,h₂⟩ := each [pinned ops₂ (C+1)] (List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl))
  rw [List.mem_singleton.mp hp] at h₁
  rw [List.mem_singleton.mp hq] at h₂
  have e₁ := ((exactPinnedPacket f baseline top z C ops₁).2.mp h₁).1
  have e₂ := ((exactPinnedPacket f baseline top z (C+1) ops₂).2.mp h₂).1
  omega

theorem joinedPacketUnsatisfiable : JoinedPacketUnsatisfiable := by
  intro f baseline top C ops₁ ops₂
  refine ⟨joinedShape ops₁ ops₂ C,?_,?_⟩
  · intro z holds
    exact noShared f baseline top C ops₁ ops₂ z ⟨_,pairChoice _ _,holds⟩
  · rintro ⟨z,live⟩
    exact noShared f baseline top C ops₁ ops₂ z live

theorem projectedSinglesSatisfiable : ProjectedSinglesSatisfiable := by
  rintro f baseline top C ops ⟨ν,tied⟩
  have hit (c z : Nat) (eq : z = c) : PacketHolds f baseline top z (pinned ops c) :=
    (exactPinnedPacket f baseline top z c ops).2.mpr ⟨eq,ν,tied⟩
  have proj (c : Nat) :=
    (exactChosenRouteProjection f baseline top C (pinned ops c) (pinnedShape ops c)).2.2.2
  have pre (c : Nat) :=
    exactSymbolicPredecessorProjection f baseline top C (pinned ops c) (pinnedShape ops c)
  refine ⟨(proj C).mpr ⟨C,Nat.le_refl C,hit C C rfl⟩,
    (proj (C+1)).mpr ⟨C+1,Nat.le_succ C,hit (C+1) (C+1) rfl⟩,fun below => ⟨?_,?_⟩⟩
  · exact (pre C).mpr ⟨C,max_le (Nat.le_refl C) below,hit C C rfl⟩
  · exact (pre (C+1)).mpr
      ⟨C+1,max_le (Nat.le_succ C) (Nat.le_trans below (Nat.le_succ C)),hit (C+1) (C+1) rfl⟩

theorem projectedJoinUnsatisfiable : ProjectedJoinUnsatisfiable := by
  intro f baseline top C ops₁ ops₂
  have shape := joinedShape ops₁ ops₂ C
  have dead := (joinedPacketUnsatisfiable f baseline top C ops₁ ops₂).2.1
  refine ⟨fun holds => ?_,fun holds => ?_⟩
  · obtain ⟨z,_,passes⟩ := (exactChosenRouteProjection f baseline top C _ shape).2.2.2.mp holds
    exact dead z passes
  · obtain ⟨z,_,passes⟩ := (exactSymbolicPredecessorProjection f baseline top C _ shape).mp holds
    exact dead z passes

private theorem prependShape (top : Nat) (q : Packet) (shape : Shape q) : Shape (prepend top q) :=
  (exactSymbolicPredecessorAppend (fun _ => 0) (fun _ => 0) top 0 q shape).1

private theorem joinedStrict (top C : Nat) (ops₁ ops₂ : List LowerOperand)
    (low₁ : StrictLower top ops₁) (low₂ : StrictLower top ops₂) :
    StrictLower top (prepend top (tuplePacket [pinned ops₁ C,pinned ops₂ (C+1)])).1 := by
  intro op member
  have tail (h : op ∈ ops₁ ++ (ops₂ ++ [])) : op.rank < top := by
    rcases List.mem_append.mp h with h | h
    · exact low₁ op h
    · rcases List.mem_append.mp h with h | h
      · exact low₂ op h
      · cases h
  by_cases zero : top = 0
  · rw [prepend,if_pos zero] at member
    change op ∈ ops₁ ++ (ops₂ ++ []) at member
    exact tail member
  · rw [prepend,if_neg zero] at member
    change op ∈ [LowerOperand.coordinate (top-1)] ++ (ops₁ ++ (ops₂ ++ [])) at member
    rcases List.mem_append.mp member with h | h
    · rw [List.mem_singleton.mp h]
      change top - 1 < top
      omega
    · exact tail h

private theorem singletonFamilyLength (top C : Nat) (q : Packet) (strict : StrictLower top q.1)
    (output : Residual) (decoded : decodeRoute C q = some output) :
    (lowerFamily top C [q]).length = 1 := by
  have allLow : (fun q : Packet => q.1.all fun op => decide (op.rank < top)) q = true :=
    List.all_eq_true.mpr fun op used => decide_eq_true (strict op used)
  have kept : keep top [q] = [q] := by
    unfold keep
    first
      | exact List.filter_cons_of_pos allLow
      | (rw [List.filter_cons_of_pos allLow]; rfl)
      | (simp only [List.filter,allLow])
      | simp [List.filter_cons,allLow]
  rw [lowerFamily,kept]
  first
    | simp [decoded]
    | (rw [List.filterMap_cons,decoded]; rfl)
    | (simp only [List.filterMap,decoded]; rfl)

private theorem joinedEmitted (top C : Nat) (ops₁ ops₂ : List LowerOperand)
    (low₁ : StrictLower top ops₁) (low₂ : StrictLower top ops₂) :
    (lowerFamily top C [prepend top (tuplePacket [pinned ops₁ C,pinned ops₂ (C+1)])]).length = 1 := by
  have shape := prependShape top _ (joinedShape ops₁ ops₂ C)
  have strict := joinedStrict top C ops₁ ops₂ low₁ low₂
  obtain ⟨output,decoded,_⟩ :=
    exactDecodedActualResidual (fun _ => 0) (fun _ => 0) top C _ shape strict
  exact singletonFamilyLength top C _ strict output decoded

theorem lowerFamilyJoinUnsatisfiable : LowerFamilyJoinUnsatisfiable := by
  intro f ρ top C ops₁ ops₂
  refine ⟨fun low₁ low₂ => joinedEmitted top C ops₁ ops₂ low₁ low₂,?_⟩
  intro p member truth
  have shapes : ∀ q ∈ [prepend top (tuplePacket [pinned ops₁ C,pinned ops₂ (C+1)])], Shape q := by
    intro q used
    rw [List.mem_singleton.mp used]
    exact prependShape top _ (joinedShape ops₁ ops₂ C)
  obtain ⟨q,used,holds⟩ := (exactActualLowerRouteFamily f ρ top C _ shapes).2.mpr ⟨p,member,truth⟩
  rw [List.mem_singleton.mp used] at holds
  exact (projectedJoinUnsatisfiable f ρ top C ops₁ ops₂).2 holds

theorem lowerFamilySinglesSatisfiable : LowerFamilySinglesSatisfiable := by
  intro f ρ top C ops live below
  have one (c : Nat) (lifted : LowerHolds f ρ top (project C (prepend top (pinned ops c)))) :
      ∃ p ∈ lowerFamily top C [prepend top (pinned ops c)], LowerMatrix f ρ p := by
    have shapes : ∀ q ∈ [prepend top (pinned ops c)], Shape q := by
      intro q used
      rw [List.mem_singleton.mp used]
      exact prependShape top _ (pinnedShape ops c)
    exact (exactActualLowerRouteFamily f ρ top C _ shapes).2.mp ⟨_,List.mem_singleton.mpr rfl,lifted⟩
  have singles := (projectedSinglesSatisfiable f ρ top C ops live).2.2 below
  exact ⟨one C singles.1,one (C+1) singles.2⟩

theorem coordinateTableLive : CoordinateTableLive := by
  intro f ρ top k below
  refine ⟨fun _ => ρ k,?_⟩
  intro j used
  have unitIndex : j < 1 := used
  have ej : j = 0 := by omega
  subst j
  refine ⟨?_,rfl⟩
  change k < top
  exact below

theorem joinRegression : JoinRegression := by
  intro f ρ top k C below pred
  have live := coordinateTableLive f ρ top k below
  have strict : StrictLower top [.coordinate k] := by
    intro op used
    rw [List.mem_singleton.mp used]
    exact below
  have singles := lowerFamilySinglesSatisfiable f ρ top C [.coordinate k] live pred
  have projected := projectedSinglesSatisfiable f ρ top C [.coordinate k] live
  have family := lowerFamilyJoinUnsatisfiable f ρ top C [.coordinate k] [.coordinate k]
  exact ⟨singles.1,singles.2,family.1 strict strict,family.2,projected.1,projected.2.1,
    (projectedJoinUnsatisfiable f ρ top C _ _).1,(joinedPacketUnsatisfiable f ρ top C _ _).2.1⟩

theorem fullActualSignedRouteJoinRegression : FullActualSignedRouteJoinRegression :=
  ⟨exactPinnedPacket,joinedPacketUnsatisfiable,projectedSinglesSatisfiable,
    projectedJoinUnsatisfiable,lowerFamilyJoinUnsatisfiable,lowerFamilySinglesSatisfiable,
    coordinateTableLive,joinRegression⟩

#print axioms joinRegression
#print axioms fullActualSignedRouteJoinRegression

end LogicLineages.PermittedControl.ActualSignedRouteJoinRegression
