import LogicLineages.PersistentMarking.NumberedWindowSimulationFootProof
import LogicLineages.PersistentMarking.NumberedWindowSimulationTraceProof
import LogicLineages.PersistentMarking.NumberedWindowSimulationRealizationProof
import LogicLineages.PersistentMarking.NumberedWindowReservedMarkWindowProof
import LogicLineages.PersistentMarking.SpineMarkingProof

namespace LogicLineages.PersistentMarking.NumberedWindowSimulationBaseCases
open LiteralDerivationTree
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowRules NumberedWindowTupleTargets
open NumberedWindowSimulationData NumberedWindowSimulationJobs
open NumberedWindowSimulationFootProof NumberedWindowSimulationTraceProof
open NumberedWindowSimulationRealizationProof
open NumberedWindowRealizationShapeProof (weakensTerm weakensArgs)

theorem variable (S : Spine.Signature) (K : List Ty) (hk : DecisionSourceUniverse.Closed K)
    (σ : Ty) (x : Nat) : Job S K (.var σ x) := by
  intro h n Q hN hQ
  cases hQ with
  | free =>
    have hw : InWindow S K E σ (.free σ x) := by
      exact window (S:=S) (n:=n) ⟨.free,True.intro⟩ (weakSource h) .free
    exact weakOfTrace hk hw rfl (.done hw.1)

theorem put (S : Spine.Signature) (K : List Ty)
    (f : Head) (bs : Spine.Args) (t : Spine.Expr)
    (hs : Spine.PaperTerm S (.head f bs) f.result) (ht : Spine.PaperTerm S t f.result)
    (d : Tree S (.weak (.marked f f.result bs .nil) t)) (ih : Job S K d) :
    Job S K (.put f bs t hs ht d) := by
  intro h n Q hN hQ
  have hb : budget d + 1 ≤ n := hN
  have hChild : Foot K d := fun ρ hp => h ρ (List.mem_append_right _ hp)
  have hw := window hs (weakSource h) hQ
  cases hQ with
  | ordinary hbReal =>
    have hR : Realizes (budget d+1) (.marked f f.result bs .nil)
        (.numbered f f.result (budget d+1) _ .nil) :=
      .marked (Nat.le_refl _) (weakensArgs hb hbReal) .nil
    have hOut := ih hChild (budget d+1) _ (Nat.le_succ _) hR
    exact prependFromContinuation hw .mark hOut

theorem strict (S : Spine.Signature) (K : List Ty) (hk : DecisionSourceUniverse.Closed K)
    (q t r : Spine.Expr) (σ : Ty) (hs : Spine.PaperTerm S q σ) (ht : Spine.PaperTerm S t σ)
    (hm : Spine.mark q = some r) (d : Tree S (.weak r t)) (ih : Job S K d) :
    Job S K (.strictIntro q t r σ hs ht hm d) := by
  intro h n Q hn hQ
  have hb : budget d + 1 ≤ n := hn
  have hChild : Foot K d := fun ρ hp => h ρ (List.mem_append_right _ hp)
  have hw := window hs (strictSource h) hQ
  obtain ⟨R,hd,hsStep,hrWin,hr⟩ := NumberedWindowReservedMarkWindowProof.reserved S K E q.type
    (budget d) q r Q hk hm (weakensTerm hb hQ) hw
  have hrt := SpineMarkingProof.markTyped E q σ r hs.1 hm
  have he : r.type = q.type := (SpineShiftProof.annotationExact E r σ hrt).trans (paperType hs).symm
  have hContinuation := ih hChild (budget d) R (Nat.le_refl _) hr
  exact ⟨R,hd,hsStep,hw,hrWin,by simpa only [he] using hContinuation⟩

end LogicLineages.PersistentMarking.NumberedWindowSimulationBaseCases
