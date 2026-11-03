module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliaryEnumerationSupportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliaryEnumerationProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedWindowEquivalence NumberedAuxiliaryCoding NumberedAuxiliaryEnumeration

theorem typeListEnumeration : NumberedAuxiliaryEnumerationTargets.ActualTypeListEnumeration := NumberedAuxiliaryEnumerationSupportProof.typeListEnumeration

theorem codeEnumeration : NumberedAuxiliaryEnumerationTargets.ActualCodeEnumeration := NumberedAuxiliaryEnumerationSupportProof.codeEnumeration

theorem sourceDepthBound : NumberedAuxiliaryEnumerationTargets.ActualSourceDepthBound := NumberedAuxiliaryEnumerationSupportProof.sourceDepthBound

theorem sourceCoverage : NumberedAuxiliaryEnumerationTargets.ActualSourceCoverage := by
  intro Symbol inst arity symbols S hc Gamma tau q L hg hl
  exact (codeEnumeration Symbol S (sourceHeads arity symbols S) L (NumberedPrimaryEquivalence.size q) Gamma.length _ (termCode q)).mpr
    ⟨NumberedAuxiliaryEnumerationSupportProof.sourceFields symbols S hc L q _ (Nat.le_refl _) hg hl,
      sourceDepthBound Symbol arity Gamma tau q⟩

theorem primaryClassCoverage : NumberedAuxiliaryEnumerationTargets.ActualPrimaryClassCoverage := by
  intro Symbol inst arity symbols S hc Gamma q r hg hp
  have hrg := (NumberedWindowEquivalenceProof.actualPrimaryConfinement Symbol arity symbols S Gamma q r hp).mp hg
  obtain ⟨hsize,hl⟩ := NumberedAuxiliaryCodingProof.primaryClassBounds Symbol arity symbols S Gamma q r hp
  have htype := NumberedPrimaryEquivalenceProof.primaryTypePreservation Symbol arity Gamma q r
    (NumberedWindowEquivalenceProof.actualPrimaryErasure Symbol arity symbols S Gamma q r hp)
  have hr := sourceCoverage Symbol inst arity symbols S hc Gamma r.1 r.2 (maxLabel q.2) hrg hl
  rw [← hsize] at hr
  exact List.mem_map.mpr ⟨termCode r.2,hr,by simp only [packedCode]; exact Prod.ext htype rfl⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliaryEnumerationProof
