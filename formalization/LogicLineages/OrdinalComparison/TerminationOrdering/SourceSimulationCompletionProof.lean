module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceSimulationCompletionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOriginalStructuralTranslationProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceSimulationCompletionProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedOriginalSourcePresentation
open NumberedOriginalStructuralTranslation NumberedOrdinaryWindow NumberedConfinedSourceSimulation
open NumberedFiniteUniverse NumberedLeastCodeRepresentative NumberedQuotientPaths LiteralContexts
open SourceSimulationCompletion SourceSimulationCompletionTargets

theorem fixedUniverseTranslationPrimitive : FixedUniverseTranslationPrimitive := by
  exact NumberedOriginalStructuralTranslationProof.windowTranslationPrimitive

theorem numericTranslationPrimitive : NumericTranslationPrimitive := by
  intro n arity Gamma
  have hd : Primrec (decodePackedSourceNumber n arity Gamma) := Primrec.decode
  exact Primrec.option_map (hd.comp Primrec.snd)
    ((fixedUniverseTranslationPrimitive n arity Gamma).comp
      ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)).to₂

theorem numericTranslationCalibration : NumericTranslationCalibration := by
  intro n arity Gamma S source
  unfold numericTr
  rw [NumberedOriginalSourcePresentationSupportProof.packedRoundTrip]
  rfl

theorem fixedUniverseSimulation : FixedUniverseSimulation := by
  intro n arity above Gamma tau s t h
  obtain ⟨hc, _, _, hs, ht⟩ :=
    NumberedConfinedSourceSimulationProof.sourceWindow n arity above Gamma tau s t h
  refine ⟨hc, hs, ht, ?_⟩
  exact NumberedOriginalStructuralTranslationProof.computedConfinedSimulation
    n arity above Gamma tau s t h

theorem arithmeticSimulation : ArithmeticSimulation := by
  intro n arity Gamma
  refine ⟨@tr n arity Gamma, fixedUniverseTranslationPrimitive n arity Gamma, ?_, ?_, ?_⟩
  · intro S
    exact ((fixedUniverseTranslationPrimitive n arity Gamma).comp
      ((Primrec.const S).pair Primrec.id)).to_comp
  · intro S source
    rfl
  · intro above tau s t h
    exact fixedUniverseSimulation n arity above Gamma tau s t h

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceSimulationCompletionProof
