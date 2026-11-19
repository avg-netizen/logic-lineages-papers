import LogicLineages.PersistentMarking.NumberedWindowSimulationHeadSupport
import LogicLineages.PersistentMarking.NumberedWindowSimulationFootProof
import LogicLineages.PersistentMarking.NumberedWindowSimulationTraceProof
import LogicLineages.PersistentMarking.NumberedWindowTraceTypingProof

namespace LogicLineages.PersistentMarking.NumberedWindowSimulationFunCase
open LiteralDerivationTree
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowPrimary NumberedWindowPreservationTargets
open NumberedWindowSimulationData NumberedWindowSimulationJobs
open NumberedWindowSimulationFootProof NumberedWindowSimulationTraceProof
open NumberedWindowSimulationRealizationProof NumberedWindowSimulationHeadSupport
open NumberedWindowPreservationGuardProof (ordinaryParts)

theorem funHead (S : Spine.Signature) (K : List Ty) (hk : DecisionSourceUniverse.Closed K)
    (f g : Head) (ss ts : Spine.Args)
    (hs : Spine.PaperTerm S (.head f ss) f.result)
    (ht : Spine.PaperTerm S (.head g ts) g.result)
    (he : Spine.Equivalent S f g) (hTy : f.result = g.result)
    (d : Tree S (.matching ss ts)) (ih : Job S K d) :
    Job S K (.funHead f g ss ts hs ht he hTy d) := by
  intro h n Q hn hQ
  have hN : budget d ≤ n := hn
  have hFoot : Foot K d := fun ρ hp => h ρ (List.mem_append_right _ hp)
  have hWin := window hs (weakSource h) hQ
  have hg := headGuard ht (weakTarget h)
  cases hQ with
  | ordinary hB =>
    obtain ⟨start,out,hPerm,hQuote,⟨tail⟩⟩ := ih hFoot n _ hN hB
    obtain ⟨tailTerm⟩ := targetTrace ht tail
    have hSt := NumberedWindowTraceTypingProof.argsStart tail
    rw [targetTypes ht] at hSt
    obtain ⟨hOrig,hf,_⟩ := ordinaryParts hWin
    have hP : Primary S K E f.result _ (.ordinary g start) :=
      .ordinary hf hg he hTy hOrig hSt hPerm
    have hTail : TypedTrace S K E f.result (.ordinary g start) (.ordinary g out) :=
      hTy.symm ▸ tailTerm
    exact weakOfTrace hk hWin (quoteHead hQuote) (.equiv hP hTail)

end LogicLineages.PersistentMarking.NumberedWindowSimulationFunCase
