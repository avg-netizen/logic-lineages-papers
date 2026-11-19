import LogicLineages.PersistentMarking.NumberedWindowSimulationBinderBridge
import LogicLineages.PersistentMarking.NumberedWindowSimulationFootProof
import LogicLineages.PersistentMarking.NumberedWindowSimulationTraceProof
import LogicLineages.PersistentMarking.NumberedWindowSimulationRealizationProof
import LogicLineages.PersistentMarking.LiteralDerivationSoundProof
import LogicLineages.PersistentMarking.ComparisonOrdinaryProof

namespace LogicLineages.PersistentMarking.NumberedWindowSimulationAbsCase
open LiteralDerivationTree NameBridge
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowTupleTargets NumberedWindowClosing
open NumberedWindowSimulationData NumberedWindowSimulationJobs NumberedWindowSimulationBinderBridge
open NumberedWindowSimulationFootProof NumberedWindowSimulationTraceProof
open NumberedWindowSimulationRealizationProof NumberedWindowPreservationTargets

private theorem bodyTyped {S σ τ s} (h : Spine.PaperTerm S (.lam σ s) (.arrow σ τ)) :
    Spine.Typed (E.push σ) s τ := by
  cases h.1 with
  | lam ht => exact ht

theorem abs (S : Spine.Signature) (K : List Ty) (hk : DecisionSourceUniverse.Closed K)
    (σ τ : Ty) (s t : Spine.Expr) (x : Nat)
    (hs : Spine.PaperTerm S (.lam σ s) (.arrow σ τ))
    (ht : Spine.PaperTerm S (.lam σ t) (.arrow σ τ))
    (hf : freeOccurs (σ,x) s = false) (hg : freeOccurs (σ,x) t = false)
    (d : Tree S (.weak (openBody σ x s) (openBody σ x t))) (ih : Job S K d) :
    Job S K (.abs σ τ s t x hs ht hf hg d) := by
  intro h n Q hn hQ
  have hBound : budget d ≤ n := hn
  have hChild : Foot K d := fun ρ hp => h ρ (List.mem_append_right _ hp)
  have hWin := window hs (weakSource h) hQ
  have hOrd : Spine.Ordinary t := ComparisonOrdinaryProof.weakOrdinary S _ (.lam σ t)
    (.abs hs ht hf hg (LiteralDerivationSoundProof.sound d))
  cases hQ with
  | lam hBody =>
    obtain ⟨T,hT,path,_⟩ := ih hChild n _ hBound (openedRealized (σ:=σ) (x:=x) hBody)
    obtain ⟨U,hU,hCloseT⟩ := targetBody (bodyTyped ht) hg hOrd hT
    have hType := SpineShiftProof.annotationExact E _ τ (openedTyped (bodyTyped hs) x)
    rw [hType] at path
    obtain ⟨out⟩ := lambdaTrace (σ:=σ) (x:=x) path
    have hCloseQ := NumberedWindowClosingAbsThinProof.absBody σ x τ s n _ (bodyTyped hs) hf hBody
    rw [hCloseQ,hCloseT] at out
    rw [paperType hs] at hWin ⊢
    exact weakOfTrace hk hWin (quoteLambda hU) out

end LogicLineages.PersistentMarking.NumberedWindowSimulationAbsCase
