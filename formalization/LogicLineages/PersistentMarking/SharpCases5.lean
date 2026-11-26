import LogicLineages.PersistentMarking.SharpBinderProof
import LogicLineages.PersistentMarking.RefinementMarkProof
import LogicLineages.PersistentMarking.ExtraCompressionProof
import LogicLineages.PersistentMarking.ExtendedEndpointProof
namespace LogicLineages.PersistentMarking.SharpCases
open Spine NameBridge SharpResults ConservativeListSupport ConservativeOwnerSupport
open ExtendedMeasure

theorem case_coverageCons (S : Signature) (n : Nat) (small : Smaller S n)
    (ha : At owners i q)
    (hc : ExtendedTree S (.strict q x))
    (hs : ExtendedTree S (.coverage owners xs))
    (hn : 1 + treeSize hc + treeSize hs = n) : Result S (.coverage owners (.cons x xs)) := by
  intro qs hq
  obtain ⟨q,hat,href⟩ := baseAt hq ha
  obtain ⟨href⟩ := href
  obtain ⟨hc'⟩ := small _ hc (by omega) q href
  obtain ⟨hs'⟩ := small _ hs (by omega) qs hq
  exact ⟨.coverageCons hat hc' hs'⟩

theorem case_wholeNil (S : Signature) (n : Nat) (small : Smaller S n)
    (hn : 1 = n) : Result S (.whole f base extras .nil) := by
  intro qb qe τ href
  exact ⟨.wholeNil⟩

theorem case_wholeCons (S : Signature) (n : Nat) (small : Smaller S n)
    (hw : ExtendedTree S (.weak (.marked f q.type base extras) q))
    (hs : ExtendedTree S (.whole f base extras qs))
    (hn : 1 + treeSize hw + treeSize hs = n) : Result S (.whole f base extras (.cons q qs)) := by
  intro qb qe τ href
  have hrt := RefinementTransitivitySupport.retype q.type href
  obtain ⟨hw'⟩ := small _ hw (by omega) _ hrt
  obtain ⟨hs'⟩ := small _ hs (by omega) qb qe τ href
  exact ⟨.wholeCons hw' hs'⟩

theorem case_orderedNil (S : Signature) (n : Nat) (small : Smaller S n)
    (hn : 1 = n) : Result S (.ordered .nil .nil) := by
  intro f base extras τ hp href
  exact ⟨.wholeNil⟩

theorem case_orderedCons (S : Signature) (n : Nat) (small : Smaller S n)
    (hw : ExtendedTree S (.weak q t))
    (hs : ExtendedTree S (.ordered qs ts))
    (hn : 1 + treeSize hw + treeSize hs = n) : Result S (.ordered (.cons q qs) (.cons t ts)) := by
  intro f base extras τ hp href
  cases href with
  | cons hchild htail =>
    obtain ⟨hs'⟩ := small _ hs (by omega) f base extras τ hp htail
    have hwhole : ExtendedWeak S (.marked f t.type base extras) t := by
      cases hchild with
      | existing ha hr =>
        obtain ⟨hc⟩ := small _ hw (by omega) _ hr
        have hf := ExtendedEndpointProof.weakFacts hc
        have htyped := hf.2.2 ▸ hf.1.1
        have howner := AuxiliaryReflexivityProof.retypePaper S f τ t.type base extras hp
        exact ⟨.select (domains := []) howner hf.2.1 (Or.inr ha) htyped rfl hc⟩
      | owner hr =>
        have hc := small _ hw (by omega) _ hr
        have heq := (ExtendedEndpointProof.weakFacts hw).2.2
        simpa only [heq] using hc
    obtain ⟨hw'⟩ := hwhole
    exact ⟨.wholeCons hw' hs'⟩

end LogicLineages.PersistentMarking.SharpCases
