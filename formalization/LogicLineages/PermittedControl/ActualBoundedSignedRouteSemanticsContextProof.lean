module
public import LogicLineages.PermittedControl.ActualBoundedSignedRouteSemanticsTargets
import LogicLineages.PermittedControl.ActualRankedNormalizationSyntaxRankProof
import LogicLineages.PermittedControl.ActualFiniteSignedNodeBranchSupportProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualBoundedSignedRouteSemantics
open ActualRankedNormalizationSyntax (extend AgreeThrough exactOriginalSupportRankExtension)
open ActualFiniteGlobalTail (syntaxOf PaidGlobalTail)
open ActualGlobalComparisonCeiling (PaidComparisonCeiling)
open ActualReadChargeIteration (ReadState RankBound Trace ZeroEdge)
open ActualZeroClassReplacement (liftedReads)
open ActualFiniteSignedNodeBranch (readTransport)
open PreparedProjection

theorem contextExtension {f B baseline r top z initial}
    (h : RunContext f B baseline r top z initial) :
    StrictMono (extend baseline top z) ∧ extend baseline top z top = z ∧
      AgreeThrough (extend baseline top z) (Function.update baseline top z) top :=
  exactOriginalSupportRankExtension baseline top z h.lower h.above

theorem contextBelow (baseline : Nat → Nat) (top z i : Nat) (lower : i < top) :
    baseline i = extend baseline top z i := by simp only [extend,if_pos lower]

theorem initialScope {f B baseline r top z initial}
    (h : RunContext f B baseline r top z initial) :
      ∀ t ∈ syntaxOf initial, t.2.rank ≤ top := by
  intro t used
  obtain ⟨rd,here,rfl⟩ := List.mem_map.mp used
  exact (h.ranks rd here).2

theorem sourceLive {f B baseline r top z initial}
    (h : RunContext f B baseline r top z initial) :
    liftedReads f (extend baseline top z) initial.reads :=
  (readTransport f (extend baseline top z) (Function.update baseline top z) top
    (contextExtension h).2.2 initial.reads (fun rd hr => (h.ranks rd hr).2)).mpr h.live

theorem paidTransfer {f B baseline r top z initial}
    (h : RunContext f B baseline r top z initial) :
    PaidGlobalTail B r (extend baseline top z) (syntaxOf initial) := by
  intro t used
  rw [(contextExtension h).2.2 _ (initialScope h t used)]
  exact h.transferTail t used

theorem paidComparison {f B baseline r top z initial}
    (h : RunContext f B baseline r top z initial) :
    PaidComparisonCeiling B r (extend baseline top z) (syntaxOf initial) := by
  intro t used
  rw [(contextExtension h).2.2 _ (initialScope h t used)]
  exact h.comparisonTail t used

theorem reachedLiveAndRank {f B ρ r top n a b} (path : Trace f B ρ r top n a b) :
    liftedReads f ρ a.reads → RankBound r top a → liftedReads f ρ b.reads ∧ RankBound r top b := by
  induction path with
  | nil s =>
      intro live range
      exact ⟨live,range⟩
  | cons edge tail ih =>
      intro _ old
      apply ih edge.live
      intro rd used
      obtain ⟨prior,seen,eq⟩ := edge.ranks rd used
      rw [eq]
      exact old prior seen

theorem snoc {f B ρ r top n a b c} (path : Trace f B ρ r top n a b) :
    ZeroEdge f B ρ r top b c → Trace f B ρ r top (n+1) a c := by
  induction path with
  | nil s =>
      intro e
      exact .cons e (.nil c)
  | cons edge rest ih =>
      intro e
      exact .cons edge (ih e)

private theorem localActual (f ρ σ : Nat → Nat) (op : LowerOperand)
    (h : ρ op.rank = σ op.rank) (v : Nat) :
    LowerOperandActual f ρ op v ↔ LowerOperandActual f σ op v := by
  cases op <;> simp only [LowerOperand.rank] at h <;> simp only [LowerOperandActual,h]

theorem tiedBelow (f ρ σ : Nat → Nat) (top : Nat) (ops : List LowerOperand) (ν : Nat → Nat)
    (h : ∀ i < top, ρ i = σ i) :
    PreparedTableTied f top ρ ops ν ↔ PreparedTableTied f top σ ops ν := by
  constructor
  · intro prior j hj
    obtain ⟨below,hit⟩ := prior j hj
    exact ⟨below,(localActual f ρ σ ops[j] (h _ below) _).mp hit⟩
  · intro prior j hj
    obtain ⟨below,hit⟩ := prior j hj
    exact ⟨below,(localActual f ρ σ ops[j] (h _ below) _).mpr hit⟩

end LogicLineages.PermittedControl.ActualBoundedSignedRouteSemantics
