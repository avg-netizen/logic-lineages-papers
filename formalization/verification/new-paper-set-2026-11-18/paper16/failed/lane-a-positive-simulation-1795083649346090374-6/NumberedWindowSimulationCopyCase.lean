import LogicLineages.PersistentMarking.NumberedWindowSimulationHeadSupport
import LogicLineages.PersistentMarking.NumberedWindowSimulationFootProof
import LogicLineages.PersistentMarking.NumberedWindowSimulationTraceProof
import LogicLineages.PersistentMarking.NumberedWindowTraceTypingProof

namespace LogicLineages.PersistentMarking.NumberedWindowSimulationCopyCase
open LiteralDerivationTree
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowRules NumberedWindowTupleTargets
open NumberedWindowPreservationTargets NumberedWindowPositiveSimulationTargets
open NumberedWindowSimulationJobs NumberedWindowSimulationHeadSupport
open NumberedWindowSimulationFootProof NumberedWindowSimulationTraceProof
open NumberedWindowSimulationRealizationProof
open NumberedWindowRealizationShapeProof (weakensArgs)

private theorem numbered {S K f g bs es ts Bs Es n k}
    (hk : DecisionSourceUniverse.Closed K)
    (hs : Spine.PaperTerm S (.marked f g.result bs es) g.result)
    (ht : Spine.PaperTerm S (.head g ts) g.result)
    (hp : Spine.Precedes S f g) (d : Tree S (.whole f bs es ts)) (ih : Job S K d)
    (h : Foot K (.copy f g bs es ts hs ht hp d))
    (hn : NumberedWindowSimulationData.budget d + 1 ≤ n)
    (hl : n ≤ k) (hb : RealizesArgs n bs Bs) (he : RealizesArgs n es Es) :
    WeakResult S K g.result (.numbered f g.result k Bs Es) (.head g ts) := by
  let b := NumberedWindowSimulationData.budget d
  have hB : b ≤ n := Nat.le_trans (Nat.le_succ _) hn
  have hChild : Foot K d := fun ρ hp => h ρ (List.mem_append_right _ hp)
  have hg := headGuard ht (weakTarget h)
  cases k with
  | zero => omega
  | succ k =>
    have hLabel : b ≤ k := by omega
    obtain ⟨out,hQuote,⟨tail⟩⟩ := ih hChild b k Bs Es (Nat.le_refl _) hLabel
      (weakensArgs hB hb) (weakensArgs hB he)
    obtain ⟨termTrace⟩ := targetTrace ht tail
    rw [targetTypes ht] at termTrace
    have hWin := window hs (weakSource h) (Realizes.marked hl hb he)
    exact weakOfTrace hk hWin (quoteHead hQuote)
      (.raw hWin.1 (NumberedWindowTraceTypingProof.termStart termTrace) (.copy hp hg) termTrace)

theorem copy (S : Spine.Signature) (K : List Ty) (hk : DecisionSourceUniverse.Closed K)
    (f g : Head) (bs es ts : Spine.Args)
    (hs : Spine.PaperTerm S (.marked f g.result bs es) g.result)
    (ht : Spine.PaperTerm S (.head g ts) g.result)
    (hp : Spine.Precedes S f g) (d : Tree S (.whole f bs es ts)) (ih : Job S K d) :
    Job S K (.copy f g bs es ts hs ht hp d) := by
  intro h n Q hn hQ
  cases hQ with
  | marked hl hb he => exact numbered hk hs ht hp d ih h hn hl hb he

end LogicLineages.PersistentMarking.NumberedWindowSimulationCopyCase
