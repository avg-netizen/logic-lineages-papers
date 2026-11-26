module
public import LogicLineages.CartierObserverCurrent.FullHigherPolesTargets
public import LogicLineages.CartierObserverCurrent.HigherPolesGeometryProof
public import LogicLineages.CartierObserverCurrent.HigherPolesResidueProof
public meta import LogicLineages.Audit
@[expose] public section
universe u v
namespace LogicLineages.CartierObserverCurrent.FullHigherPoles

theorem completeHigherPoles : Targets.CompleteHigherPoles.{u,v} := by
  refine ⟨HigherPolesWord.repeatedWord, PeriodLaurentGeneric.cartierIdentity,
    Naturality.extensionWord, ?_⟩
  intro K L _ _ _ _ _ _ σ d hd P hP
  have hg := HigherPolesGeometry.geometricRemoval K L σ d hd P hP
  refine ⟨hg.1, hg.2, ?_⟩
  intro z j
  exact HigherPolesResidue.extensionResidue K L σ _ (SourceBudget.transient d) j z

#audit_namespace LogicLineages.CartierObserverCurrent.FullHigherPoles
end LogicLineages.CartierObserverCurrent.FullHigherPoles
