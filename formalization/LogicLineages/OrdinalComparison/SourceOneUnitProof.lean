module
public import LogicLineages.OrdinalComparison.SourceOneUnitConstructionProof
public import LogicLineages.OrdinalComparison.WWSelectedBinderProof
public import LogicLineages.OrdinalComparison.SourceAbsoluteObserverProfileProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OneUnit.Proof
open AdmissibleAssignment OriginalDomain
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

theorem fullSourceOneUnit : Targets.FullSourceOneUnit := by
  refine ⟨actualHeadConstruction,?_⟩
  intro left right σ τ hσ a
  obtain ⟨h,h',ps,ps',l,l',d,ha,hv,hl,hl',hp,hp',hc,hdd,hdd',hf,hd,hscalar,hgrowth,hsem⟩ :=
    actualHeadConstruction (left++right) σ τ (a.rename (SelectedBinder.moveToHead left right σ))
  obtain ⟨w,hw,wg,wgg⟩ := source_bundle a
  have hr := SourceRenaming.Proof.assignmentNaturality (left++σ::right) (σ::(left++right)) τ
    (SelectedBinder.moveToHead left right σ) OrdinalSyntax.defaultPolicy a
  rw [hw] at hr
  change assignment OrdinalSyntax.defaultPolicy (a.rename (SelectedBinder.moveToHead left right σ))=
    some (SourceRenaming.renameVector (SelectedBinder.moveToHead left right σ) w) at hr
  have hh := Option.some.inj (ha.symm.trans hr)
  refine ⟨d,hc,w,hw,?_⟩
  intro ρ
  obtain ⟨P,R,P',R',L,L',hPpos,hRpos,hLpos,hL'pos,hPv,hRv,hP'v,hR'v,hLv,hL'v,hLval,hfree,hactive,hform⟩ := hsem ρ
  refine ⟨R,hRpos,?_,hform⟩
  rw [hh] at hRv
  change denote (valuation (unitExtension (σ := σ) ρ))
    (ordinalExpressionRename (SelectedBinder.moveToHead left right σ) (w 0))=(R : Ordinal) at hRv
  rw [AbsoluteObserver.Proof.rename_value] at hRv
  exact hRv
end LogicLineages.OrdinalComparison.Source.OneUnit.Proof
