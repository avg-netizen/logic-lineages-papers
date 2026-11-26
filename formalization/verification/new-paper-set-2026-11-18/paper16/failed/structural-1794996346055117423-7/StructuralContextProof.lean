import LogicLineages.PersistentMarking.StructuralHeadProof
import LogicLineages.PersistentMarking.StructuralBinderProof
namespace LogicLineages.PersistentMarking.StructuralContextProof
open Spine StructuralContext

theorem weakContext : StructuralStabilityTargets.WeakContext := by
  intro S C σ τ s t hc hs ht hos hot hw
  induction hc with
  | hole => exact hw
  | head hc hf hb hvb hob ha hva hoa hargs ih =>
    exact StructuralHeadProof.weak S _ _ _ _ _ _ _ _ hf hb hvb hob ha hva hoa hargs
      (StructuralFillProof.fillPaper S _ _ _ s hc hs)
      (StructuralFillProof.fillPaper S _ _ _ t hc ht) (ih hs ht hw)
  | bind hc ih =>
    exact StructuralBinderProof.weak S _ _ _ _
      (StructuralFillProof.fillPaper S _ _ _ s hc hs)
      (StructuralFillProof.fillPaper S _ _ _ t hc ht)
      (StructuralFillProof.fillOrdinary S _ _ _ t hc hot) (ih hs ht hw)

theorem strictContext : StructuralStabilityTargets.StrictContext := by
  intro S C σ τ s t hc hs ht hos hot hw
  induction hc with
  | hole => exact hw
  | head hc hf hb hvb hob ha hva hoa hargs ih =>
    exact StructuralHeadProof.strict S _ _ _ _ _ _ _ _ hf hb hvb hob ha hva hoa hargs
      (StructuralFillProof.fillPaper S _ _ _ s hc hs)
      (StructuralFillProof.fillPaper S _ _ _ t hc ht) (ih hs ht hw)
  | bind hc ih =>
    exact StructuralBinderProof.strict S _ _ _ _
      (StructuralFillProof.fillPaper S _ _ _ s hc hs)
      (StructuralFillProof.fillPaper S _ _ _ t hc ht)
      (StructuralFillProof.fillOrdinary S _ _ _ t hc hot) (ih hs ht hw)
end LogicLineages.PersistentMarking.StructuralContextProof
