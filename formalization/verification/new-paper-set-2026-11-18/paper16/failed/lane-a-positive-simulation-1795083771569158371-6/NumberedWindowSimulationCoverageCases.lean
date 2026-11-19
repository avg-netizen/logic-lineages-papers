import LogicLineages.PersistentMarking.NumberedWindowSimulationQuoteSupport
import LogicLineages.PersistentMarking.NumberedWindowSimulationOccurrenceProof
import LogicLineages.PersistentMarking.NumberedWindowTraceConsProof

namespace LogicLineages.PersistentMarking.NumberedWindowSimulationCoverageCases
open LiteralDerivationTree
open NumberedWindowSyntax NumberedWindowTupleTargets NumberedWindowOrdinaryTranslation
open NumberedWindowTraceAlgebra NumberedWindowSimulationData NumberedWindowSimulationJobs
open NumberedWindowSimulationOccurrenceProof NumberedWindowSimulationQuoteSupport

theorem nil (S : Spine.Signature) (K : List Ty) (owners : Spine.Args) :
    Job S K (.coverageNil owners) := by
  intro h n as hn hA
  exact ⟨.nil,.nil,rfl,fun _ h => False.elim (List.not_mem_nil h),⟨.done .nil⟩⟩

theorem cons (S : Spine.Signature) (K : List Ty)
    (owners : Spine.Args) (i : Nat) (q x : Spine.Expr) (xs : Spine.Args)
    (hAt : Spine.At owners i q) (d : Tree S (.strict q x))
    (more : Tree S (.coverage owners xs)) (ih : Job S K d) (ihC : Job S K more) :
    Job S K (.coverageCons owners i q x xs hAt d more) := by
  intro h n As hn hRep
  have hb : max (budget d) (budget more) ≤ n := hn
  have hd : Foot K d := fun ρ hp => h ρ (List.mem_append_right _ (List.mem_append_left _ hp))
  have ht : Foot K more := fun ρ hp => h ρ (List.mem_append_right _ (List.mem_append_right _ hp))
  obtain ⟨Q,hGet,hQ⟩ := realizedAt hAt hRep
  obtain ⟨R,hdMark,_hRaw,_hWinQ,_hWinR,T,hT,trace,_⟩ :=
    ih hd n Q (Nat.le_trans (Nat.le_max_left _ _) hb) hQ
  obtain ⟨starts,outs,hQuote,hOrigin,⟨tail⟩⟩ :=
    ihC ht n As (Nat.le_trans (Nat.le_max_right _ _) hb) hRep
  obtain ⟨out,_⟩ := NumberedWindowTraceConsProof.cons S K E x.type (types xs)
    R T starts outs (align hT trace) tail
  refine ⟨.cons R starts,.cons T outs,quoteCons hT hQuote,?_,⟨out⟩⟩
  intro a ha
  change a ∈ R :: starts.toList at ha
  rcases List.mem_cons.mp ha with rfl | hA
  · exact ⟨Q,getMem As i Q hGet,hdMark⟩
  · exact hOrigin a hA

end LogicLineages.PersistentMarking.NumberedWindowSimulationCoverageCases
