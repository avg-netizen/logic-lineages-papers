module

public import LogicLineages.NativeModule.PersistentMarking.CutSelectionSupport

@[expose] public section

namespace LogicLineages.PersistentMarking.CutSelectionProof
open Spine ExtendedMeasure

theorem selection : CutSelectionTargets.Selection := by
  intro S n below f sb se g tb te τ q i domains args r u root hp ht hu ha hq htuple hcall continuation hbound ho
  have hqtype := SpineShiftProof.annotationExact _ _ _ hq
  have hqpaper : PaperTerm S q (ArrowPrefix domains τ) := ⟨hq,CutSelectionSupport.selectedValid ht ha⟩
  have hargs := CutSelectionSupport.tupleRelated root hp ht htuple
  have hright : CallTyped EmptyContext q.type args τ := by
    rw [hqtype]
    exact ConservativeOwnerSupport.tupleTyped S g τ tb te ht htuple τ
  have hwhole : CallTyped EmptyContext (ArrowPrefix domains τ) (ownerCopies f sb se domains) τ :=
    ConservativeOwnerSupport.tupleTyped S f τ sb se hp (ConservativeOwnerSupport.wholeTuple f sb se domains) τ
  rcases CutOwnerProof.selected S f sb se g tb te q i root ha with ⟨p,j,hpAt,hpq⟩ | howner
  · have hpp := CutEdgeProof.leftPaper hpq hqpaper
    have hptype := SpineShiftProof.annotationExact _ _ _ hpp.1
    have hleft : CallTyped EmptyContext p.type (ownerCopies f sb se domains) τ := hptype.symm ▸ hwhole
    obtain ⟨out,hout,hresult⟩ := ApplicationCovarianceProof.fullApplication S p q _ args τ r hpq hargs hleft hright hcall
    obtain ⟨hcut⟩ := below out r u continuation hbound ho hresult
    exact ⟨.select hp hu hpAt hpp.1 hout hcut⟩
  · rw [hqtype] at howner
    have hleft : CallTyped EmptyContext (Expr.marked f (ArrowPrefix domains τ) sb se).type (ownerCopies f sb se domains) τ := hwhole
    obtain ⟨out,hout,hresult⟩ := ApplicationCovarianceProof.fullApplication S (.marked f (ArrowPrefix domains τ) sb se) q _ args τ r howner hargs hleft hright hcall
    have hshape := ConservativeOwnerSupport.ownerApplication S f τ sb se hp domains
    have heq : out = .marked f τ sb (se.append (ownerCopies f sb se domains)) := Option.some.inj (hout.symm.trans hshape)
    subst out
    obtain ⟨hcut⟩ := below _ r u continuation hbound ho hresult
    exact ⟨.copies hp hu (ConservativeOwnerSupport.wholeCopies f sb se domains) hcut⟩
end LogicLineages.PersistentMarking.CutSelectionProof
