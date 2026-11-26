import LogicLineages.PersistentMarking.OrdinaryCompositionTargets
import LogicLineages.PersistentMarking.CutCoreProof
import LogicLineages.PersistentMarking.AuxiliaryEmbeddingProof
import LogicLineages.PersistentMarking.ElementaryProof
namespace LogicLineages.PersistentMarking.OrdinaryCompositionProof
open Spine

theorem weakWeak : OrdinaryCompositionTargets.WeakWeak := by
  intro S s t u hs ht hu hst htu
  exact CutCoreProof.fullCut S s t u (AuxiliaryEmbeddingProof.embedWeak S s t hst)
    (AuxiliaryEmbeddingProof.embedWeak S t u htu) hu

theorem strictWeak : OrdinaryCompositionTargets.StrictWeak := by
  intro S s t u hs ht hu hst htu
  cases hst with
  | @intro s σ t marked hp hmid hm hw =>
    have hright := AuxiliaryEmbeddingProof.embedWeak S t u htu
    have hcut := CutCoreProof.fullCut S marked t u (AuxiliaryEmbeddingProof.embedWeak S marked t hw) hright hu
    exact .intro hp (CutEdgeProof.rightPaper hright hmid) hm hcut

theorem weakStrict : OrdinaryCompositionTargets.WeakStrict := by
  intro S s t u hs ht hu hst htu
  have hleft := AuxiliaryEmbeddingProof.embedWeak S s t hst
  cases htu with
  | @intro t σ u marked hp htarget hm hw =>
    obtain ⟨source,hsource⟩ := ExtendedMarkabilityProof.reflectMarkability S s t marked hleft hm
    have hmarked := ExtendedMarkingProof.forward S s t hleft
    rw [SpineMarkingProof.markHeadmark s source hsource,SpineMarkingProof.markHeadmark t marked hm] at hmarked
    have hcut := CutCoreProof.fullCut S source marked u hmarked (AuxiliaryEmbeddingProof.embedWeak S marked u hw) hu
    exact .intro (CutEdgeProof.leftPaper hleft hp) htarget hsource hcut

theorem strictStrict : OrdinaryCompositionTargets.StrictStrict := by
  intro S s t u hs ht hu hst htu
  exact weakStrict S s t u hs ht hu (ElementaryProof.strictIncluded S s t hst) htu

theorem fullComposition : OrdinaryCompositionTargets.FullComposition :=
  ⟨weakWeak,weakStrict,strictWeak,strictStrict⟩
end LogicLineages.PersistentMarking.OrdinaryCompositionProof
