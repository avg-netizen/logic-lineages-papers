import LogicLineages.PersistentMarking.NumberedWindowSimulationSelectCore
import LogicLineages.PersistentMarking.NumberedWindowSimulationFootProof
import LogicLineages.PersistentMarking.NumberedWindowSimulationTraceProof
import LogicLineages.PersistentMarking.NumberedWindowTraceContextsProof

namespace LogicLineages.PersistentMarking.NumberedWindowSimulationSelectCase
open LiteralDerivationTree
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowRules
open NumberedWindowTupleTargets NumberedWindowSimulationJobs
open NumberedWindowSimulationFootProof NumberedWindowSimulationTraceProof
open NumberedWindowSimulationRealizationProof
open NumberedWindowPositiveSimulationTargets

private theorem atNumbered {S K f τ bs es t i q ds r n k Bs Es}
    (hk : DecisionSourceUniverse.Closed K)
    (ho : Spine.PaperTerm S (.marked f τ bs es) τ) (ht : Spine.PaperTerm S t τ)
    (ha : Spine.At bs i q ∨ Spine.At es i q) (hq : Spine.Typed E q (Spine.ArrowPrefix ds τ))
    (hr : Spine.apply q (Spine.ownerCopies f bs es ds) = some r)
    (d : Tree S (.weak r t)) (ih : Job S K d)
    (h : Foot K (.select f τ bs es t i q ds r ho ht ha hq hr d))
    (hn : NumberedWindowSimulationData.budget (.select f τ bs es t i q ds r ho ht ha hq hr d) ≤ n)
    (hl : n ≤ k) (hb : RealizesArgs n bs Bs) (he : RealizesArgs n es Es) :
    WeakResult S K τ (.numbered f τ k Bs Es) t := by
  let b := NumberedWindowSimulationData.budget d
  let costs := NumberedWindowTupleTargets.budget b (Spine.ownerCopies f bs es ds)
  have hn' : b + (Spine.ownerCopies f bs es ds).length + 2 ≤ n := hn
  have hInput : costs ≤ n := by dsimp only [costs,NumberedWindowTupleTargets.budget]; omega
  have hs : SymbolicAdmissible K q := fun ρ hp => localBound h ρ
    (List.mem_append_right _ (List.mem_append_left _ (List.mem_append_left _ hp)))
  have hc : SymbolicArgsAdmissible K (Spine.ownerCopies f bs es ds) := fun ρ hp =>
    localBound h ρ (List.mem_append_right _ (List.mem_append_right _ hp))
  have hChild : Foot K d := fun ρ hp => h ρ (List.mem_append_right _ hp)
  cases k with
  | zero => omega
  | succ k =>
    have hLabel : costs ≤ k := by dsimp only [costs,NumberedWindowTupleTargets.budget]; omega
    have hWin := window ho (weakSource h) (Realizes.marked hl hb he)
    obtain ⟨start,out,hsStep,hPath,hOut⟩ :=
      NumberedWindowSimulationSelectCore.reduction hk ho ha hq hs hc hr hb he hInput hLabel
    obtain ⟨path,_⟩ := NumberedWindowTraceContextsProof.fromWindowPath S K E τ start out hPath
    have hResume := ih hChild b out (Nat.le_refl _) hOut
    have hType : r.type = τ := NumberedWindowSimulationRealizationProof.realizesAtType hOut
      (NumberedWindowApplicationPathProof.endpoints hPath).2.1
    have hNext : WeakResult S K τ out t := by simpa only [hType] using hResume
    have hStart := (NumberedWindowApplicationPathProof.endpoints hPath).1
    exact prepend hWin hStart hsStep (prependTyped hk hStart path hNext)

theorem select (S : Spine.Signature) (K : List Ty) (hk : DecisionSourceUniverse.Closed K)
    (f : Head) (τ : Ty) (bs es : Spine.Args) (t : Spine.Expr) (i : Nat)
    (q : Spine.Expr) (ds : List Ty) (r : Spine.Expr)
    (ho : Spine.PaperTerm S (.marked f τ bs es) τ) (ht : Spine.PaperTerm S t τ)
    (ha : Spine.At bs i q ∨ Spine.At es i q) (hq : Spine.Typed E q (Spine.ArrowPrefix ds τ))
    (hr : Spine.apply q (Spine.ownerCopies f bs es ds) = some r)
    (d : Tree S (.weak r t)) (ih : Job S K d) :
    Job S K (.select f τ bs es t i q ds r ho ht ha hq hr d) := by
  intro h n Q hn hQ
  cases hQ with
  | marked hl hb he => exact atNumbered hk ho ht ha hq hr d ih h hn hl hb he

end LogicLineages.PersistentMarking.NumberedWindowSimulationSelectCase
