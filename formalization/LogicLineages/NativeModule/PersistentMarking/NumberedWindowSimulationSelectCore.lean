module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowSimulationOccurrenceProof
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowTupleSplitChecks

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowSimulationSelectCore
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowRules NumberedWindowTupleTargets
open NumberedWindowSimulationJobs NumberedWindowSimulationOccurrenceProof
open Spine (At ArrowPrefix)
open NumberedWindowRealizationShapeProof (termShape weakensArgs weakensTerm)

theorem reduction {S K f τ bs es Bs Es q r ds i n k b}
    (hk : DecisionSourceUniverse.Closed K)
    (ho : Spine.PaperTerm S (.marked f τ bs es) τ)
    (ha : At bs i q ∨ At es i q)
    (hq : Spine.Typed E q (ArrowPrefix ds τ))
    (hs : SymbolicAdmissible K q)
    (hc : SymbolicArgsAdmissible K (Spine.ownerCopies f bs es ds))
    (hCall : Spine.apply q (Spine.ownerCopies f bs es ds) = some r)
    (hb : RealizesArgs n bs Bs) (he : RealizesArgs n es Es)
    (hInput : NumberedWindowTupleTargets.budget b (Spine.ownerCopies f bs es ds) ≤ n)
    (hLabel : NumberedWindowTupleTargets.budget b (Spine.ownerCopies f bs es ds) ≤ k) :
    ∃ start out, RawStep S K (.numbered f τ (k+1) Bs Es) start ∧
      WindowPath S K E τ start out ∧ Realizes b r out := by
  have hSel : ∃ Q, (Bs.get i = some Q ∨ Es.get i = some Q) ∧ Realizes n q Q := by
    rcases ha with hb' | he'
    · obtain ⟨Q,hGet,hQ⟩ := realizedAt hb' hb
      exact ⟨Q,Or.inl hGet,hQ⟩
    · obtain ⟨Q,hGet,hQ⟩ := realizedAt he' he
      exact ⟨Q,Or.inr hGet,hQ⟩
  have hVal : Spine.Valid S q :=
    ha.elim (fun h => atValid h ho.2.2.1) (fun h => atValid h ho.2.2.2)
  obtain ⟨Q,hGet,hQ⟩ := hSel
  have hArrow : Q.type = ArrowPrefix ds τ :=
    (termShape hQ).1.trans (SpineShiftProof.annotationExact E q _ hq)
  have hCopies := ownerRealized (f:=f) hLabel (weakensArgs hInput hb) (weakensArgs hInput he) ds
  obtain ⟨start,out,hApps,hPath,hOut⟩ :=
    NumberedWindowTupleSplitChecks.exact_WholeTupleSimulation S K [] q r
      (Spine.ownerCopies f bs es ds) (ArrowPrefix ds τ) τ b Q (ownerCopies f k Bs Es ds)
      hk hq hVal (callOwner f τ bs es ds ho.1) (ownerValid ho.2 ds) hs hc hCall
      (weakensTerm hInput hQ) hCopies
  exact ⟨start,out,.select hGet hArrow hApps,hPath,hOut⟩

end LogicLineages.PersistentMarking.NumberedWindowSimulationSelectCore
