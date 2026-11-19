import LogicLineages.PersistentMarking.NumberedWindowSimulationJobs
import LogicLineages.PersistentMarking.NumberedWindowOrdinaryDomainProof
import LogicLineages.PersistentMarking.NumberedWindowClosingAbsThinProof
import LogicLineages.PersistentMarking.NumberedWindowClosingTraceThinProof
import LogicLineages.PersistentMarking.NumberedWindowTraceContextsProof
import LogicLineages.PersistentMarking.NumberedWindowRealizationSubstitutionProof
import LogicLineages.PersistentMarking.SpineSubstitutionProof

namespace LogicLineages.PersistentMarking.NumberedWindowSimulationBinderBridge
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowTupleTargets NumberedWindowClosing
open NumberedWindowPreservationTargets NumberedWindowOrdinaryTranslation NumberedWindowSimulationJobs
open NameBridge (openBody)

theorem openedTyped {σ τ body} (h : Spine.Typed (E.push σ) body τ) (x : Nat) :
    Spine.Typed E (openBody σ x body) τ :=
  SpineSubstitutionProof.parallelPreserves E [σ] _ body τ (.cons .free .nil) h

theorem openedRealized {n σ x q Q} (h : Realizes n q Q) :
    Realizes n (openBody σ x q) (substitute (.cons (.free σ x) .nil) 0 Q) :=
  NumberedWindowRealizationSubstitutionProof.term (.cons .free .nil) h 0

theorem targetBody {σ τ x q T} (h : Spine.Typed (E.push σ) q τ)
    (hf : NameBridge.freeOccurs (σ,x) q = false) (ho : Spine.Ordinary q)
    (hT : tr (openBody σ x q) = some T) :
    ∃ U, tr q = some U ∧ closeAt (σ,x) 0 T = U := by
  obtain ⟨U,hU⟩ := (NumberedWindowOrdinaryDomainProof.termDomain q).mpr ho
  have hReal := ((NumberedWindowOrdinaryQuoteProof.term q U hU).2 0).1
  have hOpened := openedRealized (σ:=σ) (x:=x) hReal
  have e := ((NumberedWindowOrdinaryQuoteProof.term _ T hT).2 0).2 _ hOpened
  exact ⟨U,hU,by
    rw [← e]
    exact NumberedWindowClosingAbsThinProof.absBody σ x τ q 0 U h hf hReal⟩

theorem lambdaTrace {S K σ τ x Q T} (h : TypedTrace S K E τ Q T) :
    Nonempty (TypedTrace S K E (.arrow σ τ)
      (.lam σ (closeAt (σ,x) 0 Q)) (.lam σ (closeAt (σ,x) 0 T))) := by
  have hc : CloseCompatible (σ,x) 0 E (E.push σ) := ⟨rfl,fun _ _ h => by cases h⟩
  obtain ⟨closed,_⟩ := NumberedWindowClosingTraceThinProof.trace hc h
  obtain ⟨out,_⟩ := NumberedWindowTraceContextsProof.lambda S K E σ τ _ _ closed
  exact ⟨out⟩

theorem quoteLambda {σ t T} (h : tr t = some T) :
    tr (.lam σ t) = some (.lam σ T) := by simp only [tr,h,Option.map_some]

end LogicLineages.PersistentMarking.NumberedWindowSimulationBinderBridge
