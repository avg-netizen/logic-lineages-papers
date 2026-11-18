import LogicLineages.PersistentMarking.PortFAbsProof
import LogicLineages.PersistentMarking.PortListCasesProof
import LogicLineages.PersistentMarking.PortTermCasesProof
namespace LogicLineages.PersistentMarking.PortNormalizationProof
open Spine NameBridge PortNormalization RefinementRenamingTargets RefinementRenameSupport

theorem weak (S : Signature) (F : Inputs S) (q t : Expr) (h : Spine.Weak S q t) : WeakMotive F q t := by
  refine Spine.Weak.rec
    (motive_1 := fun q t _ => WeakMotive F q t)
    (motive_2 := fun q t _ => StrictMotive F q t)
    (motive_3 := fun qs ts _ => MatchingMotive F qs ts)
    (motive_4 := fun qs ts _ => MultisetMotive F qs ts)
    (motive_5 := fun qs ts _ => CoverageMotive F qs ts)
    (motive_6 := fun f bs es ts _ => WholeMotive F f bs es ts)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  · intros; intro π Γ hp hw hu ho; exact .var
  · intros; rename_i hs ht hx hy child ih
    exact PortAbsProof.absCase S F _ _ _ _ _ hs ht hx hy ih
  · intros; rename_i hs ht he hty child ih
    exact PortTermCasesProof.funCase S F _ _ _ _ hs ht he hty ih
  · intros; rename_i hs ht child ih
    exact PortTermCasesProof.putCase S F _ _ _ hs ht ih
  · intros; rename_i hs ht ha hq hc child ih
    exact PortTermCasesProof.selectCase S F _ _ _ _ _ _ _ _ _ hs ht ha hq hc ih
  · intros; rename_i hs ht hx hy child ih
    exact PortFAbsProof.fabsCase S F _ _ _ _ _ _ _ hs ht hx hy ih
  · intros; rename_i hs ht hp child ih
    exact PortTermCasesProof.copyCase S F _ _ _ _ _ hs ht hp ih
  · intros; rename_i hs ht he hm hw ihm ihw
    exact PortTermCasesProof.statCase S F _ _ _ _ _ hs ht he ihm ihw
  · intros; rename_i hs ht hm child ih
    exact PortTermCasesProof.strictCase S F _ _ _ _ hs ht hm ih
  · intro π Γ hp hw hu ho; exact .nil
  · intros; rename_i hr hw hm ihw ihm
    exact PortListCasesProof.matchingCons S F _ _ _ _ _ hr ihw ihm
  · intros; rename_i hs ht hn hm hc ihm ihc
    exact PortListCasesProof.multisetReplace S F _ _ _ _ _ _ hs ht hn ihm ihc
  · intros; intro π Γ hp hw hu ho; exact .nil
  · intros; rename_i ha hs hc ihs ihc
    exact PortListCasesProof.coverageCons S F _ _ _ _ _ ha ihs ihc
  · intros; intro π Γ hp hw hu ho; exact .nil
  · intros; rename_i hw hs ihw ihs
    exact PortListCasesProof.wholeCons S F _ _ _ _ _ ihw ihs

theorem strict (S : Signature) (F : Inputs S) (q t : Expr) (h : Spine.Strict S q t) : StrictMotive F q t := by
  cases h with
  | intro hs ht hm hw => exact PortTermCasesProof.strictCase S F _ _ _ _ hs ht hm (weak S F _ _ hw)

theorem matching (S : Signature) (F : Inputs S) (qs ts : Args) (h : Spine.Matching S qs ts) : MatchingMotive F qs ts := by
  cases qs with
  | nil => cases h; intro π Γ hp hw hu ho; exact .nil
  | cons q qs => cases h with
    | cons hr hw hm => exact PortListCasesProof.matchingCons S F _ _ _ _ _ hr (weak S F _ _ hw) (matching S F _ _ hm)
termination_by sizeOf qs

theorem coverage (S : Signature) (F : Inputs S) (qs ts : Args) (h : Spine.Coverage S qs ts) : CoverageMotive F qs ts := by
  cases ts with
  | nil => cases h; intro π Γ hp hw hu ho; exact .nil
  | cons t ts => cases h with
    | cons ha hs hc => exact PortListCasesProof.coverageCons S F _ _ _ _ _ ha (strict S F _ _ hs) (coverage S F _ _ hc)
termination_by sizeOf ts

theorem multiset (S : Signature) (F : Inputs S) (qs ts : Args) (h : Spine.Multiset S qs ts) : MultisetMotive F qs ts := by
  cases h with
  | replace hs ht hn hm hc => exact PortListCasesProof.multisetReplace S F _ _ _ _ _ _ hs ht hn (matching S F _ _ hm) (coverage S F _ _ hc)

theorem whole (S : Signature) (F : Inputs S) (f : Head) (bs es ts : Args) (h : Spine.Whole S f bs es ts) : WholeMotive F f bs es ts := by
  cases ts with
  | nil => cases h; intro π Γ hp hw hu ho; exact .nil
  | cons t ts => cases h with
    | cons hw hs => exact PortListCasesProof.wholeCons S F _ _ _ _ _ (weak S F _ _ hw) (whole S F _ _ _ _ hs)
termination_by sizeOf ts

theorem normalization : PortNormalizationTargets.Normalization := fun S F =>
  ⟨weak S F,strict S F,matching S F,multiset S F,coverage S F,whole S F⟩
end LogicLineages.PersistentMarking.PortNormalizationProof
