module
public import LogicLineages.PermittedControl.ActualSignedOrdinaryPairHighTargets
import LogicLineages.PermittedControl.ActualSignedOrdinaryPairHighValueProof
import LogicLineages.PermittedControl.ActualSignedOrdinaryPairHighPaidProof
import LogicLineages.PermittedControl.StableSortedHighFieldPacketProof
import LogicLineages.PermittedControl.StableSortedHighFieldValuesProof
import LogicLineages.PermittedControl.StableSortedHighFieldGuardProof
import LogicLineages.PermittedControl.OriginalMatrixLinearRowFormulaShapeProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualSignedOrdinaryPairHigh
open OrdinalComparison FieldComparison PreparedProjection
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open StableSortedHighField (basePacket guardedPacket orderGuard appendOrderShape basePacketExact
  actualGuardedPacket baseMeaning orderGuardEval)
open OriginalMatrixLinearRowFormula (safePolarity choosePolarity)

private theorem restrict (f ρ : Nat → Nat) (lo hi : Nat) (ops : List LowerOperand) (ν : Nat → Nat)
    (tied : PreparedTableTied f hi ρ (ops ++ [.coordinate lo]) ν) :
    PreparedTableTied f hi ρ ops ν ∧ ν (ops.length+1) = ρ lo := by
  have lookup (j : Nat) (used : j < ops.length) :
      (ops ++ [LowerOperand.coordinate lo]).get ⟨j,by simpa using Nat.lt_succ_of_lt used⟩ = ops.get ⟨j,used⟩ :=
    List.getElem_append_left used
  have last : (ops ++ [LowerOperand.coordinate lo]).get ⟨ops.length,by simp⟩ =
      LowerOperand.coordinate lo := by
    change (ops ++ [LowerOperand.coordinate lo])[ops.length] = _
    rw [List.getElem_append_right (le_refl ops.length)]
    simp
  constructor
  · intro j used
    have bigger : j < (ops ++ [LowerOperand.coordinate lo]).length := by simpa using Nat.lt_succ_of_lt used
    have read := tied j bigger
    simpa only [lookup j used] using read
  · have read := (tied ops.length (by simp)).2
    rw [last] at read
    exact read

private theorem updateReserved (f ρ : Nat → Nat) (hi : Nat) (ops : List LowerOperand)
    (ν : Nat → Nat) (z : Nat) (tied : PreparedTableTied f hi ρ ops ν) :
    PreparedTableTied f hi ρ ops (Function.update ν 0 z) := by
  intro j hj
  have eq : (Function.update ν 0 z) (j+1) = ν (j+1) :=
    Function.update_of_ne (Nat.succ_ne_zero j) z ν
  change ops[j].rank < hi ∧ LowerOperandActual f ρ ops[j] ((Function.update ν 0 z) (j+1))
  rw [eq]
  exact tied j hj

private theorem sameRankOps (F G : ValueField) (lo wanted : Nat) (paid : wanted ≤ 2)
    (op : LowerOperand) (used : op ∈ (basePacket F G lo wanted).1 ++ [.coordinate lo]) :
    op.rank = lo := by
  cases shape : distinctForm (normalizeShortField F) (normalizeShortField G) with
  | const a =>
      have eq : op = .coordinate lo := by simpa [basePacket,paid,shape] using used
      rw [eq]
      rfl
  | linear sign H =>
      have eq : op = .ordinary lo H ∨ op = .coordinate lo := by
        simpa [basePacket,paid,shape] using used
      rcases eq with rfl | rfl <;> rfl

theorem exactStrictSignedPair : ExactStrictSignedPair := by
  intro f B selected F G hF hG ρ lo hi rankOrder paid c nz k positive
  let wanted := (request k c).1
  let base := basePacket F G lo wanted
  let ops := base.1 ++ [.coordinate lo]
  let bit := wantedBit k c positive
  have wantedRange : wanted ≤ 2 := by
    cases k <;> by_cases pos : 0 < c <;> simp [wanted,request,pos]
  have cmpPay : highFieldComparisonBoundCode B (longFieldCode F) (longFieldCode G) ≤ ρ lo :=
    (le_max_left _ _).trans paid
  have shape := (basePacketExact F G lo hi wanted rankOrder).2
  have tied := (actualGuardedPacket f B selected F G hF hG ρ lo hi wanted rankOrder cmpPay).2.1
  refine ⟨appendOrderShape base.1 _ lo (safePolarity base.1 base.2 shape bit),
    sameRankOps F G lo wanted wantedRange,tied,?_⟩
  intro ν fit z ordered θ
  let slots := Function.update ν 0 z
  have loV : θ lo = ρ lo := Function.update_of_ne (ne_of_lt rankOrder) z ρ
  have hiV : θ hi = z := by simp [θ]
  have slotZ : slots 0 = z := by simp [slots]
  have minPaid : minimum B F G ≤ min (θ lo) (θ hi) := by
    simpa only [loV,hiV,min_eq_left ordered.le] using paid
  obtain ⟨dF,dG,u,v,hu,hv,unique⟩ := guardedFields f B selected F G hF hG θ lo hi minPaid
  refine ⟨dF,dG,bothLiteralHits f θ F G lo hi u v hu hv,?_⟩
  have fitUpdated : PreparedTableTied f hi ρ ops slots := updateReserved f ρ hi ops ν z fit
  obtain ⟨fitBase,raw⟩ := restrict f ρ lo hi base.1 slots fitUpdated
  have actualStrict : ρ lo < slots 0 := by rwa [slotZ]
  have guard : (orderGuard (base.1.length+1)).eval slots :=
    (orderGuardEval _ slots).mpr (by rwa [raw])
  have actual : StableSortedHighField.actualOutcome f F G (ρ lo) (slots 0) wanted ↔
      numericalComparison u v = wanted := by
    rw [slotZ,← loV,← hiV]
    constructor
    · rintro ⟨a,b,av,bv,eq⟩
      obtain ⟨ea,eb⟩ := unique a b av bv
      simpa only [ea,eb] using eq
    · intro cmp
      exact ⟨u,v,hu.2,hv.2,cmp⟩
  have compute : base.2.eval slots ↔ numericalComparison u v = wanted :=
    (baseMeaning f B selected F G hF hG ρ lo hi wanted cmpPay slots fitBase actualStrict).trans actual
  have polarity := polarityMeaning base.2 bit slots (numericalComparison u v = wanted) compute
  have sign := exactSignedPairValue f θ F G lo hi u v c nz hu hv k positive
  change ((orderGuard (base.1.length+1)).eval slots ∧ (choosePolarity base.2 bit).eval slots) ↔
    source f θ F G lo hi c k positive
  exact (and_iff_right guard).trans (polarity.trans sign.symm)

end LogicLineages.PermittedControl.ActualSignedOrdinaryPairHigh
