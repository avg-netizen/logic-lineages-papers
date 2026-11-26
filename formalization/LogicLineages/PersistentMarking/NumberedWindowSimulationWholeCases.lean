import LogicLineages.PersistentMarking.NumberedWindowSimulationQuoteSupport
import LogicLineages.PersistentMarking.NumberedWindowTraceConsProof

namespace LogicLineages.PersistentMarking.NumberedWindowSimulationWholeCases
open LiteralDerivationTree
open NumberedWindowSyntax NumberedWindowTupleTargets NumberedWindowSimulationData NumberedWindowSimulationJobs
open NumberedWindowSimulationQuoteSupport

theorem nil (S : Spine.Signature) (K : List Ty) (f : Head) (bs es : Spine.Args) :
    Job S K (.wholeNil f bs es) := by
  intro h n k Bs Es hb hl hBs hEs
  exact ⟨.nil,rfl,⟨.done .nil⟩⟩

theorem cons (S : Spine.Signature) (K : List Ty)
    (f : Head) (q : Spine.Expr) (bs es qs : Spine.Args)
    (d : Tree S (.weak (.marked f q.type bs es) q)) (more : Tree S (.whole f bs es qs))
    (ih : Job S K d) (ihW : Job S K more) :
    Job S K (.wholeCons f q bs es qs d more) := by
  intro h n k Bs Es hn hl hb he
  have hMax : max (budget d) (budget more) ≤ n := hn
  have hd : Foot K d := fun ρ hp => h ρ (List.mem_append_right _ (List.mem_append_left _ hp))
  have hw : Foot K more := fun ρ hp => h ρ (List.mem_append_right _ (List.mem_append_right _ hp))
  obtain ⟨T,hT,p,_⟩ := ih hd n (.numbered f q.type k Bs Es)
    (Nat.le_trans (Nat.le_max_left _ _) hMax) (.marked hl hb he)
  obtain ⟨Ts,hTs,⟨tail⟩⟩ :=
    ihW hw n k Bs Es (Nat.le_trans (Nat.le_max_right _ _) hMax) hl hb he
  obtain ⟨out,_⟩ := NumberedWindowTraceConsProof.cons S K E q.type (types qs) _ T _ Ts p tail
  exact ⟨.cons T Ts,quoteCons hT hTs,⟨out⟩⟩

end LogicLineages.PersistentMarking.NumberedWindowSimulationWholeCases
