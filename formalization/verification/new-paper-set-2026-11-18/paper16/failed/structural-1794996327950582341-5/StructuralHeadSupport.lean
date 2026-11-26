import LogicLineages.PersistentMarking.StructuralFillProof
import LogicLineages.PersistentMarking.StructuralSubstitutionProof
namespace LogicLineages.PersistentMarking.StructuralHeadSupport
open Spine

theorem atFacts (S : Signature) (qs : Args) (types : List Ty)
    (ht : BaseTyped EmptyContext qs types) (hv : ValidArgs S qs) (ho : OrdinaryArgs qs)
    (ha : At qs i q) : PaperTerm S q q.type ∧ Ordinary q := by
  cases ha with
  | here =>
    cases ht with
    | cons hq hqs =>
      have he := SpineShiftProof.annotationExact _ _ _ hq
      exact ⟨⟨he.symm ▸ hq,hv.1⟩,ho.1⟩
  | there ha =>
    cases ht with
    | cons hq hqs => exact atFacts S _ _ hqs hv.2 ho.2 ha
termination_by sizeOf qs

theorem atPrefix (prefix rest : Args) (ha : At rest i q) :
    ∃ j, At (prefix.append rest) j q := by
  cases prefix with
  | nil => exact ⟨i,ha⟩
  | cons x xs =>
    obtain ⟨j,hj⟩ := atPrefix xs rest ha
    exact ⟨j+1,.there hj⟩
termination_by sizeOf prefix

theorem slotSuppliers (S : Signature) (before after : Args) (bt at : List Ty) (s t : Expr)
    (hb : BaseTyped EmptyContext before bt) (hvb : ValidArgs S before) (hob : OrdinaryArgs before)
    (ha : BaseTyped EmptyContext after at) (hva : ValidArgs S after) (hoa : OrdinaryArgs after)
    (hw : Weak S s t) : ∀ i q, At (before.append (.cons t after)) i q →
      ∃ j x, At (before.append (.cons s after)) j x ∧ Weak S x q := by
  intro i q hq
  cases before with
  | nil =>
    cases hq with
    | here => exact ⟨0,s,.here,hw⟩
    | @there qs i q x hq =>
      have hp := atFacts S after at ha hva hoa hq
      exact ⟨i+1,q,.there hq,ElementaryProof.ordinaryReflexive S q q.type hp.1 hp.2⟩
  | cons b bs =>
    cases hb with
    | cons hbt hbs =>
      cases hq with
      | here => exact ⟨0,b,.here,ElementaryProof.ordinaryReflexive S b _ ⟨hbt,hvb.1⟩ hob.1⟩
      | there hq =>
        obtain ⟨j,x,hx,hwx⟩ := slotSuppliers S bs after _ at s t hbs hvb.2 hob.2 ha hva hoa hw _ _ hq
        exact ⟨j+1,x,.there hx,hwx⟩
termination_by sizeOf before

theorem wholeSuppliers (S : Signature) (f : Head) (base targets : Args)
    (hf : Admitted S f) (hb : BaseTyped EmptyContext base f.arguments) (hv : ValidArgs S base)
    (hs : ∀ i q, At targets i q → ∃ j x, At base j x ∧ Weak S x q) : Whole S f base .nil targets := by
  cases targets with
  | nil => exact .nil
  | cons q qs =>
    obtain ⟨j,x,hx,hw⟩ := hs 0 q .here
    obtain ⟨htree⟩ := AuxiliaryEmbeddingProof.embedWeak S x q hw
    have facts := ExtendedEndpointProof.weakFacts htree
    have hxt : Typed EmptyContext x q.type := facts.2.2 ▸ facts.1.1
    have howner : PaperTerm S (.marked f q.type base .nil) q.type := ⟨.marked hb .nil,hf,hv,True.intro⟩
    exact .cons (.select howner facts.2.1 (Or.inl hx) hxt rfl hw)
      (wholeSuppliers S f base qs hf hb hv (fun i q hq => hs (i+1) q (.there hq)))
termination_by sizeOf targets

theorem splitKeep (xs : Args) : Split xs xs .nil := by
  cases xs with
  | nil => exact .nil
  | cons q qs => exact .left (splitKeep qs)
termination_by sizeOf xs

theorem splitSlot (before after : Args) (q : Expr) :
    Split (before.append (.cons q after)) (before.append after) (.cons q .nil) := by
  cases before with
  | nil => exact .right (splitKeep after)
  | cons x xs => exact .left (splitSlot xs after q)
termination_by sizeOf before

theorem matchingSlot (S : Signature) (before after : Args) (bt at : List Ty) (s t : Expr)
    (hb : BaseTyped EmptyContext before bt) (hvb : ValidArgs S before) (hob : OrdinaryArgs before)
    (ha : BaseTyped EmptyContext after at) (hva : ValidArgs S after) (hoa : OrdinaryArgs after)
    (hw : Weak S s t) : Matching S (before.append (.cons s after)) (before.append (.cons t after)) := by
  cases before with
  | nil => exact .cons .here hw (ElementaryProof.matchingRefl S after at ha hva hoa)
  | cons q qs =>
    cases hb with
    | cons hq hqs =>
      exact .cons .here (ElementaryProof.ordinaryReflexive S q _ ⟨hq,hvb.1⟩ hob.1)
        (matchingSlot S qs after _ at s t hqs hvb.2 hob.2 ha hva hoa hw)
termination_by sizeOf before
end LogicLineages.PersistentMarking.StructuralHeadSupport
