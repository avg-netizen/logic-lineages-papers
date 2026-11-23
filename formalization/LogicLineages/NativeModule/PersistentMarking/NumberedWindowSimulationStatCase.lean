module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowSimulationHeadSupport
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowSimulationFootProof
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowSimulationTraceProof
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowTraceTypingProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowSimulationStatCase
open LiteralDerivationTree
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowTupleTargets
open NumberedWindowPositiveSimulationTargets NumberedWindowSimulationJobs
open NumberedWindowSimulationHeadSupport NumberedWindowSimulationFootProof NumberedWindowSimulationTraceProof
open NumberedWindowSimulationRealizationProof
open NumberedWindowSimulationData (budget)
open NumberedWindowRealizationShapeProof (weakensArgs)

private theorem numbered {S K f g bs es ts Bs Es n k}
    (hk : DecisionSourceUniverse.Closed K)
    (hs : Spine.PaperTerm S (.marked f g.result bs es) g.result)
    (ht : Spine.PaperTerm S (.head g ts) g.result) (heq : Spine.Equivalent S f g)
    (m : Tree S (.multiset bs ts)) (w : Tree S (.whole f bs es ts))
    (ihM : Job S K m) (ihW : Job S K w)
    (h : Foot K (.stat f g bs es ts hs ht heq m w))
    (hn : max (budget m) (budget w) + 1 ≤ n)
    (hl : n ≤ k) (hb : RealizesArgs n bs Bs) (he : RealizesArgs n es Es) :
    WeakResult S K g.result (.numbered f g.result k Bs Es) (.head g ts) := by
  let b := max (budget m) (budget w)
  have hM : Foot K m := fun ρ hp => h ρ (List.mem_append_right _ (List.mem_append_left _ hp))
  have hW : Foot K w := fun ρ hp => h ρ (List.mem_append_right _ (List.mem_append_right _ hp))
  have hB : b ≤ n := Nat.le_trans (Nat.le_succ _) hn
  have hg := headGuard ht (weakTarget h)
  cases k with
  | zero => omega
  | succ k =>
    have hLabel : b ≤ k := by omega
    have hWhole := ihW hW b k Bs Es (Nat.le_max_right _ _) hLabel
      (weakensArgs hB hb) (weakensArgs hB he)
    obtain ⟨_,_sameTarget,_wholeCall⟩ := hWhole
    obtain ⟨start,out,hQuote,hPrimitive,⟨tail⟩⟩ := ihM hM n Bs
      (Nat.le_trans (Nat.le_max_left _ _) hB) hb
    obtain ⟨termTrace⟩ := targetTrace ht tail
    have hWin := window hs (weakSource h) (Realizes.marked hl hb he)
    exact weakOfTrace hk hWin (quoteHead hQuote)
      (.raw hWin.1 (NumberedWindowTraceTypingProof.termStart termTrace)
        (.stat heq hg hPrimitive) termTrace)

theorem stat (S : Spine.Signature) (K : List Ty) (hk : DecisionSourceUniverse.Closed K)
    (f g : Head) (bs es ts : Spine.Args)
    (hs : Spine.PaperTerm S (.marked f g.result bs es) g.result)
    (ht : Spine.PaperTerm S (.head g ts) g.result) (heq : Spine.Equivalent S f g)
    (m : Tree S (.multiset bs ts)) (w : Tree S (.whole f bs es ts))
    (ihM : Job S K m) (ihW : Job S K w) :
    Job S K (.stat f g bs es ts hs ht heq m w) := by
  intro h n Q hn hQ
  cases hQ with
  | marked hl hb he => exact numbered hk hs ht heq m w ihM ihW h hn hl hb he

end LogicLineages.PersistentMarking.NumberedWindowSimulationStatCase
