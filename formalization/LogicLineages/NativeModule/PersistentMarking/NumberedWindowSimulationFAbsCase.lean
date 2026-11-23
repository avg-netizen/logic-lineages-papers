module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowSimulationBinderBridge
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowSimulationOccurrenceProof
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowSimulationFootProof
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowSimulationTraceProof
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowClosingFAbsProof
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowTraceTypingProof
public import LogicLineages.NativeModule.PersistentMarking.LiteralDerivationSoundProof
public import LogicLineages.NativeModule.PersistentMarking.ComparisonOrdinaryProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowSimulationFAbsCase
open LiteralDerivationTree NameBridge
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowRules NumberedWindowTupleTargets
open NumberedWindowSimulationJobs NumberedWindowSimulationBinderBridge
open NumberedWindowSimulationFootProof NumberedWindowSimulationTraceProof
open NumberedWindowSimulationRealizationProof NumberedWindowPositiveSimulationTargets
open NumberedWindowPreservationTargets

private theorem bodyTyped {S σ τ body} (h : Spine.PaperTerm S (.lam σ body) (.arrow σ τ)) :
    Spine.Typed (E.push σ) body τ := by
  cases h.1 with
  | lam hb => exact hb

private theorem numbered {S K f σ τ bs es body x Bs Es n k}
    (hk : DecisionSourceUniverse.Closed K)
    (hs : Spine.PaperTerm S (.marked f (.arrow σ τ) bs es) (.arrow σ τ))
    (ht : Spine.PaperTerm S (.lam σ body) (.arrow σ τ))
    (hf : freeOccurs (σ,x) (.marked f (.arrow σ τ) bs es) = false)
    (hg : freeOccurs (σ,x) body = false)
    (d : Tree S (.weak (.marked f τ bs (es.append (.cons (.free σ x) .nil))) (openBody σ x body)))
    (ih : Job S K d) (h : Foot K (.fabs f σ τ bs es body x hs ht hf hg d))
    (hn : NumberedWindowSimulationData.budget d + 1 ≤ n)
    (hl : n ≤ k) (hb : RealizesArgs n bs Bs) (he : RealizesArgs n es Es) :
    WeakResult S K (.arrow σ τ) (.numbered f (.arrow σ τ) k Bs Es) (.lam σ body) := by
  let b := NumberedWindowSimulationData.budget d
  have hB : b ≤ n := Nat.le_trans (Nat.le_succ _) hn
  have hChild : Foot K d := fun ρ hp => h ρ (List.mem_append_right _ hp)
  have hOrd : Spine.Ordinary body := ComparisonOrdinaryProof.weakOrdinary S _ (.lam σ body)
    (.fabs hs ht hf hg (LiteralDerivationSoundProof.sound d))
  cases k with
  | zero => omega
  | succ k =>
    have hk' : b ≤ k := by omega
    let openQ : NTerm := .numbered f τ k Bs (Es.append (.cons (.free σ x) .nil))
    have hEs := NumberedWindowSimulationOccurrenceProof.appendRealized b es
      (.cons (.free σ x) .nil) Es (.cons (.free σ x) .nil)
      (NumberedWindowRealizationShapeProof.weakensArgs hB he) (.cons .free .nil)
    have hR : Realizes b (.marked f τ bs (es.append (.cons (.free σ x) .nil))) openQ :=
      .marked hk' (NumberedWindowRealizationShapeProof.weakensArgs hB hb) hEs
    obtain ⟨T,hT,path,_⟩ := ih hChild b openQ (Nat.le_refl _) hR
    obtain ⟨U,hU,hCloseT⟩ := targetBody (bodyTyped ht) hg hOrd hT
    obtain ⟨out⟩ := lambdaTrace (σ:=σ) (x:=x) path
    have hCloseQ := NumberedWindowClosingFAbsProof.ownerBody f σ τ x bs es n k Bs Es hs.1 hf hb he
    change NumberedWindowClosing.closeAt (σ,x) 0 openQ = _ at hCloseQ
    rw [hCloseQ,hCloseT] at out
    have hWin := window hs (weakSource h) (Realizes.marked hl hb he)
    exact weakOfTrace hk hWin (quoteLambda hU)
      (.raw hWin.1 (NumberedWindowTraceTypingProof.termStart out) .fabs out)

theorem fabs (S : Spine.Signature) (K : List Ty) (hk : DecisionSourceUniverse.Closed K)
    (f : Head) (σ τ : Ty) (bs es : Spine.Args) (body : Spine.Expr) (x : Nat)
    (hs : Spine.PaperTerm S (.marked f (.arrow σ τ) bs es) (.arrow σ τ))
    (ht : Spine.PaperTerm S (.lam σ body) (.arrow σ τ))
    (hf : freeOccurs (σ,x) (.marked f (.arrow σ τ) bs es) = false)
    (hg : freeOccurs (σ,x) body = false)
    (d : Tree S (.weak (.marked f τ bs (es.append (.cons (.free σ x) .nil))) (openBody σ x body)))
    (ih : Job S K d) : Job S K (.fabs f σ τ bs es body x hs ht hf hg d) := by
  intro h n Q hn hQ
  cases hQ with
  | marked hl hb he => exact numbered hk hs ht hf hg d ih h hn hl hb he

end LogicLineages.PersistentMarking.NumberedWindowSimulationFAbsCase
