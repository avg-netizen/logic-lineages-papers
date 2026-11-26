module
public import LogicLineages.CartierObserverCurrent.FullGenericCountTargets
public import LogicLineages.CartierObserverCurrent.FullSinglePredecessorProof
public import LogicLineages.OrdinalComparison.ParametricActualCollapseProof
public import LogicLineages.OrdinalComparison.ControlScheduleProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.CartierObserverCurrent.FullGenericCount
open LogicLineages.OrdinalComparison
open LogicLineages.OrdinalComparison.ParametricActualCollapse

private theorem stepValue (f : Nat → Nat) (hf : StrictMono f) (hi : ∀ n, n < f n)
    (a : Ordinal.{0}) (ha : a < epsilonZero) (hn : Ordinal.omega0 ≤ a) :
    collapseWith f a = collapseWith f (actualControlledStep f a) + 1 := by
  have hd := actualNonfiniteDecomposition a hn ha
  have h := FullSinglePredecessor.genericRecurrence f hf hi (actualLimitPart a)
    hd.1 hd.2.1 (actualTailPart a)
  rw [←hd.2.2.1] at h
  rw [←hd.2.2.2] at h
  exact h

private theorem traceValue (f : Nat → Nat) (hf : StrictMono f) (hi : ∀ n, n < f n)
    (a : Ordinal.{0}) (ha : a < epsilonZero) :
    ∀ i : Nat, i ≤ actualControlledCount f a →
      collapseWith f a = collapseWith f (actualControlledStateAfter f a i) + i := by
  intro i
  induction i with
  | zero => intro _; simp only [actualControlledStateAfter_zero, Nat.add_zero]
  | succ i ih =>
    intro hb
    have hlt : i < actualControlledCount f a := by omega
    have hs := (actualControlledTraceFirstFinite f a ha).2 i hlt.le
    have hv := stepValue f hf hi _ hs.1 (hs.2.2 hlt)
    rw [ih hlt.le, hv, actualControlledStateAfter_succ]
    omega

theorem completeCount : Targets.CompleteCount := by
  intro f hf hi lam hlam hlim t ht
  let a := lam + ((t - actualOrdinalNorm lam : Nat) : Ordinal)
  let τ := actualControlledCount f a
  have ha := actualFiniteTailClosureNorm lam hlam (t - actualOrdinalNorm lam)
  have han : actualOrdinalNorm a = t := by
    change actualOrdinalNorm (lam + ((t - actualOrdinalNorm lam : Nat) : Ordinal)) = t
    rw [ha.2]
    omega
  have hinf : Ordinal.omega0 ≤ a :=
    (Ordinal.omega0_le_of_isSuccLimit hlim).trans le_self_add
  have htrace := actualControlledTraceFirstFinite f a ha.1
  have hpos : 0 < τ := by
    have hc := (actualControlledCountRecursion f a ha.1).2 hinf
    dsimp [τ]
    omega
  obtain ⟨Z,hZ⟩ := Ordinal.lt_omega0.mp htrace.1
  have hnZ : actualOrdinalNorm (actualControlledStateAfter f a τ) = Z := by
    rw [hZ]
    exact (ParametricActualCollapse.Proof.natural_facts Z).2
  refine ⟨hpos, ?_, ?_, ?_, ?_⟩
  · rw [hnZ]
    exact hZ
  · intro i hit
    exact (htrace.2 i hit.le).2.2 hit
  · have hn := actualControlledNormIteration f a ha.1 τ le_rfl
    rw [han] at hn
    exact hn
  · have hv := traceValue f hf hi a ha.1 τ le_rfl
    rw [hZ, ParametricActualCollapse.Proof.finiteValues f (fun n => (hi n).le) Z] at hv
    rw [hnZ]
    exact hv

#audit_namespace LogicLineages.CartierObserverCurrent.FullGenericCount
end LogicLineages.CartierObserverCurrent.FullGenericCount
