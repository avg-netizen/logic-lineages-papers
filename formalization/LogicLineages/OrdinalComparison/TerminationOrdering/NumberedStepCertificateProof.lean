module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedStepCertificateTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedStepCertificateProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedWindowReduction NumberedLeastCodeRepresentative NumberedNumericDecoding NumberedCopyCertificate NumberedStepContexts NumberedTypedFocus NumberedNumericRoot NumberedStepCertificate

theorem stepCertificateSound : NumberedStepCertificateTargets.ActualStepCertificateSound := by
  intro n arity symbols S Gamma table tau q r certificate h
  cases hf : focus certificate.path q with
  | none => simp [stepTest,hf] at h
  | some f =>
    cases hb : decodePackedNumber n arity f.holeGamma certificate.replacement with
    | none => simp [stepTest,hf,hb] at h
    | some b =>
      obtain ⟨sigma,b⟩ := b
      cases hc : decodeSelector n arity f.holeGamma certificate.root with
      | none => simp [stepTest,hf,hb,hc] at h
      | some selector =>
        simp only [stepTest,hf,hb,hc] at h
        split at h
        next ht =>
          cases ht
          have hh : selectorTest n arity symbols S f.holeGamma table ⟨f.holeType,f.value⟩ ⟨f.holeType,b⟩ selector=true ∧
              packedNumber (⟨tau,plug f.context b⟩ : Packed (Fin n) arity Gamma)=packedNumber (⟨tau,r⟩ : Packed (Fin n) arity Gamma) := by simpa using h
          have hr := (NumberedNumericRootProof.typedRootSelectors n arity symbols S f.holeGamma table _ _).mp ⟨selector,hh.1⟩
          have hs := NumberedRootDecompositionProof.rootTyped hr
          have hw := NumberedStepContextsProof.liftTerm symbols S (tableAbove table) f.value b hs f.context
          have hsource := NumberedTypedFocusProof.termFocusReconstruction n arity certificate.path Gamma tau q f hf
          have hp := NumberedLeastCodeRepresentativeProof.packedNumberInjective n arity Gamma hh.2
          have htarget : plug f.context b=r := by simpa using hp
          rw [hsource,htarget] at hw
          exact hw
        next => contradiction

theorem stepCertificateComplete : NumberedStepCertificateTargets.ActualStepCertificateComplete := by
  intro n arity symbols S Gamma table tau q r h
  obtain ⟨HG,HT,a,b,context,rfl,rfl,hr⟩ := (NumberedRootDecompositionProof.termRootDecomposition n arity symbols S (tableAbove table) Gamma tau q r).mp h
  obtain ⟨path,hf⟩ := NumberedTypedFocusProof.termFocusCoverage n arity HG HT Gamma tau context a
  obtain ⟨selector,hs⟩ := (NumberedNumericRootProof.typedRootSelectors n arity symbols S HG table ⟨HT,a⟩ ⟨HT,b⟩).mpr hr
  have hb : decodePackedNumber n arity HG (packedNumber (⟨HT,b⟩ : Packed (Fin n) arity HG))=some ⟨HT,b⟩ := NumberedNumericDecodingProof.packedNumericRoundTrip n arity HG ⟨HT,b⟩
  have hc : decodeSelector n arity HG (selectorNumber selector)=some selector := NumberedNumericRootProof.rootSelectorRoundTrip n arity HG selector
  refine ⟨⟨path,packedNumber (⟨HT,b⟩ : Packed (Fin n) arity HG),selectorNumber selector⟩,?_⟩
  simp [stepTest,hf,hb,hc,hs]

theorem stepCertificateConfinement : NumberedStepCertificateTargets.ActualStepCertificateConfinement := by
  intro n arity symbols S hc Gamma table tau q r certificate h hq
  exact NumberedWindowReductionProof.stepGood symbols S hc (stepCertificateSound n arity symbols S Gamma table tau q r certificate h) hq

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedStepCertificateProof
