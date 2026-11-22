module
public import LogicLineages.PermittedControl.ActualSelectedSignedRoutePacketTargets
import LogicLineages.PermittedControl.ActualPreparedSlotAppendProof
import LogicLineages.PermittedControl.ActualPreparedSlotAppendReadProof
import LogicLineages.PermittedControl.PreparedParameterActualProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualSelectedSignedRoutePacket
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open PreparedProjection
open ActualPreparedSlotAppend (Packet append view merge shiftName exactPreparedAppend exactAppendedReads)
open ActualSignedOrdinaryPairHigh (OrderTest)
open ActualBoundedSignedRoutes (Tip Route PacketHolds TipHolds RouteHolds)

private theorem viewUpdate (d : Nat) (ν : Nat → Nat) (z : Nat) :
    view d (Function.update ν 0 z) = Function.update (view d ν) 0 z := by
  funext n
  cases n with
  | zero => simp [view,shiftName]
  | succ j =>
      have h₁ : d+(j+1) ≠ 0 := by omega
      simp only [view,shiftName,Function.update_of_ne h₁,Function.update_of_ne (Nat.succ_ne_zero j)]

private theorem mergeUpdate (d : Nat) (l r : Nat → Nat) (z : Nat) :
    merge d (Function.update l 0 z) (Function.update r 0 z) =
      Function.update (merge d l r) 0 z := by
  funext n
  by_cases h : n = 0
  · subst n
    simp [merge]
  · by_cases left : n ≤ d
    · simp [merge,left,h]
    · have tail : n-d ≠ 0 := by omega
      simp [merge,left,h,tail]

theorem exactRouteAppend : ExactRouteAppend := by
  intro f baseline top z l r hl hr
  have shape := exactPreparedAppend l r hl hr
  have reads := exactAppendedReads f baseline top l.1 r.1
  refine ⟨shape.1,?_⟩
  constructor
  · rintro ⟨ν,tied,passes⟩
    obtain ⟨tl,tr⟩ := (reads.2.2.1 ν).mp tied
    have iffEval := shape.2.1 (Function.update ν 0 z)
    rw [viewUpdate] at iffEval
    obtain ⟨left,right⟩ := iffEval.mp passes
    exact ⟨⟨ν,tl,left⟩,⟨view l.1.length ν,tr,right⟩⟩
  · rintro ⟨⟨ν,tl,left⟩,⟨μ,tr,right⟩⟩
    refine ⟨merge l.1.length ν μ,reads.2.2.2 ν μ tl tr,?_⟩
    have shared : Function.update ν 0 z 0 = Function.update μ 0 z 0 := by simp
    have passes := (shape.2.2 (Function.update ν 0 z) (Function.update μ 0 z) shared).mpr ⟨left,right⟩
    rw [mergeUpdate] at passes
    exact passes

private theorem exactTip (f baseline : Nat → Nat) (top z : Nat) (test : OrderTest)
    (positive : Bool) (tip : Tip) :
    PacketHolds f baseline top z (terminalPacket test positive tip) ↔
      TipHolds f baseline top z test positive tip := by
  cases tip with
  | linear p => rfl
  | signed c =>
    have evalEmpty (a : NormalForm.Formula) :
        PacketHolds f baseline top z ([],a) ↔ ∃ ν : Nat → Nat, a.eval (Function.update ν 0 z) := by
      constructor
      · rintro ⟨ν,_,holds⟩; exact ⟨ν,holds⟩
      · rintro ⟨ν,holds⟩
        exact ⟨ν,fun j used => False.elim (Nat.not_lt_zero j used),holds⟩
    have bitMeaning : signedBit test c = true ↔ test.test.Holds c := by
      cases test <;> simp [signedBit,ActualSignedOrdinaryPairHigh.OrderTest.test,
        SignedRowGuardedTest.Test.Holds]
    by_cases holds : test.test.Holds c
    · have hit : signedBit test c = true := bitMeaning.mpr holds
      cases positive <;> simp [terminalPacket,TipHolds,evalEmpty,hit,
        SignedRowGuardedTest.Test.atPolarity,NormalForm.Formula.eval,holds]
    · have misses : signedBit test c ≠ true := fun hit => holds (bitMeaning.mp hit)
      have hit : signedBit test c = false := by simpa using misses
      cases positive <;> simp [terminalPacket,TipHolds,evalEmpty,hit,
        SignedRowGuardedTest.Test.atPolarity,NormalForm.Formula.eval,holds]

private theorem foldHolds (f baseline : Nat → Nat) (top z : Nat)
    (tip : Packet) (ht : Shape tip) (gs : List Packet) (hs : ∀ p ∈ gs, Shape p) :
    Shape (gs.foldr append tip) ∧
      (PacketHolds f baseline top z (gs.foldr append tip) ↔
        (∀ p ∈ gs, PacketHolds f baseline top z p) ∧ PacketHolds f baseline top z tip) := by
  induction gs with
  | nil =>
    refine ⟨ht,?_⟩
    exact ⟨fun t => ⟨fun p h => False.elim (List.not_mem_nil h),t⟩,And.right⟩
  | cons p ps ih =>
    have tail := ih (fun q h => hs q (List.mem_cons_of_mem _ h))
    have pack := exactRouteAppend f baseline top z p (ps.foldr append tip)
      (hs p List.mem_cons_self) tail.1
    refine ⟨pack.1,pack.2.trans ?_⟩
    constructor
    · rintro ⟨h,t⟩
      obtain ⟨all,last⟩ := tail.2.mp t
      refine ⟨fun q used => ?_,last⟩
      rcases List.mem_cons.mp used with first | rest
      · simpa only [first] using h
      · exact all q rest
    · rintro ⟨all,last⟩
      exact ⟨all p List.mem_cons_self,tail.2.mpr
        ⟨fun q used => all q (List.mem_cons_of_mem _ used),last⟩⟩

theorem exactSelectedRoutePacket : ExactSelectedRoutePacket := by
  intro f baseline top z test positive path hg ht
  have fold := foldHolds f baseline top z _ ht path.guards hg
  refine ⟨fold.1,fold.2.trans (and_congr Iff.rfl (exactTip f baseline top z test positive path.tip)),?_⟩
  intro ν tied j hj
  exact (preparedTiedProjection.1 f baseline _ _).mpr (tied j hj).2

end LogicLineages.PermittedControl.ActualSelectedSignedRoutePacket
