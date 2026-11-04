module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOriginalStructuralTranslationTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOriginalStructuralTranslationProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedNumericDecoding NumberedLeastCodeRepresentative
open NumberedOriginalSourcePresentation NumberedOriginalSourcePresentationProof NumberedOriginalStructuralTranslation
open NumberedConfinedSourceSimulation NumberedQuotientPaths NumberedOrdinaryWindow LiteralContexts

attribute [local irreducible] representativeCode

theorem originalTranslationPrimitive : NumberedOriginalStructuralTranslationTargets.ActualOriginalTranslationPrimitive := by
  intro n arity Gamma
  have he : Primrec (fun p : PackedSource (Fin n) arity Gamma => packedSourceNumber p) := Primrec.encode
  have hd : Primrec (fun p : PackedSource (Fin n) arity Gamma => decodePackedNumber n arity Gamma (packedSourceNumber p)) :=
    (NumberedPackedCodecPrimrecProof.packedDecoderPrimitive n arity Gamma).comp he
  have h := Primrec.option_getD.comp hd
    (Primrec.const (⟨Ty.ground,AuxTerm.bottom Ty.ground⟩ : Packed (Fin n) arity Gamma))
  apply h.of_eq
  intro p
  change (decodePackedNumber n arity Gamma (packedNumber (packedTranslation p))).getD _=packedTranslation p
  rw [NumberedNumericDecodingProof.packedNumericRoundTrip]
  rfl

theorem windowTranslationPrimitive : NumberedOriginalStructuralTranslationTargets.ActualWindowTranslationPrimitive := by
  intro n arity Gamma
  have hi : Primrec (fun p : List Ty × PackedSource (Fin n) arity Gamma =>
      ((symbols n,p.1),packedTranslation p.2)) :=
    (((Primrec.const (symbols n)).pair Primrec.fst).pair ((originalTranslationPrimitive n arity Gamma).comp Primrec.snd))
  exact (NumberedRepresentativePrimrecProof.representativePrimitive n arity Gamma).comp hi

theorem sharedWindowPrimitive : NumberedOriginalStructuralTranslationTargets.ActualSharedWindowPrimitive := by
  intro n arity Gamma
  have hw : Primrec (fun p : PackedSource (Fin n) arity Gamma × PackedSource (Fin n) arity Gamma =>
      Source.SourcePortContexts.literalTypes p.1.2) :=
    (NumberedOriginalSourceWindowProof.packedSourceWindowPrimitive n arity Gamma).comp Primrec.fst
  exact ((windowTranslationPrimitive n arity Gamma).comp (hw.pair Primrec.fst)).pair
    ((windowTranslationPrimitive n arity Gamma).comp (hw.pair Primrec.snd))

theorem numericTranslationPrimitive : NumberedOriginalStructuralTranslationTargets.ActualNumericTranslationPrimitive := by
  intro n arity Gamma
  have hd : Primrec (decodePackedSourceNumber n arity Gamma) := Primrec.decode
  have hb : Primrec (fun p : (Nat × Nat) × PackedSource (Fin n) arity Gamma =>
      (decodePackedSourceNumber n arity Gamma p.1.2).map (fun t => sourceAnchoredCodes p.2 t)) :=
    Primrec.option_map (hd.comp (Primrec.snd.comp Primrec.fst))
      ((sharedWindowPrimitive n arity Gamma).comp ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)).to₂
  have h := Primrec.option_bind (hd.comp Primrec.fst) hb.to₂
  have hc : Primrec (fun p : Nat × Nat => numericTranslation n arity Gamma p.1 p.2) :=
    h.of_eq (fun p => by simp only [numericTranslation,Option.map_eq_bind,Function.comp_def,
      Option.bind_eq_bind,Option.pure_def])
  exact hc.to₂

theorem numericCalibration : NumberedOriginalStructuralTranslationTargets.ActualNumericCalibration := by
  intro n arity Gamma source target
  unfold numericTranslation
  rw [NumberedOriginalSourcePresentationSupportProof.packedRoundTrip]
  simp only [Option.bind_eq_bind,Option.bind_some]
  rw [NumberedOriginalSourcePresentationSupportProof.packedRoundTrip]
  rfl

theorem computedConfinedSimulation : NumberedOriginalStructuralTranslationTargets.ActualComputedConfinedSimulation := by
  intro n arity above Gamma tau s t h
  exact NumberedConfinedSourceSimulationProof.strictQuotientPath n arity above Gamma tau s t h

theorem genuineComputedSimulation : NumberedOriginalStructuralTranslationTargets.ActualGenuineComputedSimulation := by
  intro n arity Gamma
  refine ⟨fun p => sourceAnchoredCodes p.1 p.2,(sharedWindowPrimitive n arity Gamma).to_comp,fun _ _ => rfl,?_⟩
  intro above tau s t h
  exact computedConfinedSimulation n arity above Gamma tau s t h

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOriginalStructuralTranslationProof
