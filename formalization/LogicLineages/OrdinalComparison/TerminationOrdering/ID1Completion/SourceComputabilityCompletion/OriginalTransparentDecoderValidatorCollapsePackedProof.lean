module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalScalarProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapsePackedProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalAcceptanceSupportProof InternalAcceptanceConjunctionProof
open InternalBetaTotalityProof (addHyp)
open OriginalLambdaConstructorGraphSyntaxProof (andIntro andLeft andRight)
open OriginalTypedDecoderStepSpecification OriginalTypedDecoderInternalScalarProof
open OriginalRawSyntaxTransportInternalParserSupportProof (programsCases)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- The four selectors are the literal packed type/raw and original Gamma/context
selectors. Their order matches the original guarded source checker. -/
theorem fieldValues (packed parameter typ raw c gamma : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (StepPair packed typ raw)))
    (hc : Nonempty (Derivation body Delta (StepPair parameter c gamma))) :
    ∀ i : Fin 4, Nonempty (Derivation body Delta
      (programGraph ((![leftOf (.projection 0),rightOf (.projection 0),
        rightOf (.projection 1),leftOf (.projection 1)] : Fin 4 → Program 2) i)
        (![typ,raw,gamma,c] i) ![packed,parameter])) := by
  intro i
  let xs : Fin 2 → OTerm alpha := ![packed,parameter]
  exact Fin.cases
    (pairLeftValue (.projection 0) packed typ raw xs (projectionValue 0 xs) hp)
    (Fin.cases
      (pairRightValue (.projection 0) packed typ raw xs (projectionValue 0 xs) hp)
      (Fin.cases
        (pairRightValue (.projection 1) parameter c gamma xs (projectionValue 1 xs) hc)
        (Fin.cases
          (pairLeftValue (.projection 1) parameter c gamma xs (projectionValue 1 xs) hc)
          (fun k => Fin.elim0 k)))) i

/-- Every arithmetic packed input and parameter have their actual original
pair fields. No decoding, typing, calibration or acceptance premise is needed. -/
theorem packedCases (packed parameter : OTerm alpha) (psi : Formula alpha)
    (step : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (typ raw c gamma : OTerm beta),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (StepPair (packed.relabel j) typ raw)) →
      Nonempty (Derivation body Theta (StepPair (parameter.relabel j) c gamma)) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  let ps : Fin 4 → Program 2 := ![leftOf (.projection 0),rightOf (.projection 0),
    rightOf (.projection 1),leftOf (.projection 1)]
  apply programsCases ps (Fin.cons packed (Fin.cons parameter Fin.elim0)) psi
  intro beta j Theta ys hj hs
  simp only [consTermRename,emptyRename] at hs
  let xs : Fin 2 → OTerm beta := ![packed.relabel j,parameter.relabel j]
  exact step beta j Theta (ys 0) (ys 1) (ys 3) (ys 2) hj
    (pairFields (.projection 0) (packed.relabel j) (ys 0) (ys 1) xs
      (projectionValue 0 xs) (hs 0) (hs 1))
    (pairFields (.projection 1) (parameter.relabel j) (ys 3) (ys 2) xs
      (projectionValue 1 xs) (hs 3) (hs 2))

theorem targetFieldsIntro (H G : Program 1)
    (packed parameter typ raw c gamma : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (StepPair packed typ raw)))
    (hc : Nonempty (Derivation body Delta (StepPair parameter c gamma)))
    (hg : Nonempty (Derivation body Delta (graph1 G (numeral 1) c)))
    (ht : Nonempty (Derivation body Delta
      (OriginalTypedDecoderInternalAcceptance.TermAccepted H typ raw gamma))) :
    Nonempty (Derivation body Delta
      (graph2 (OriginalTypedDecoder.target H G) (numeral 1) packed parameter)) := by
  let xs : Fin 2 → OTerm alpha := ![packed,parameter]
  have hv := fieldValues packed parameter typ raw c gamma hp hc
  apply conjunctionAccept _ _ xs
  · exact unaryValue G (leftOf (.projection 1)) (numeral 1) c xs hg (hv 3)
  · apply compositionValue (OriginalTypedDecoder.termCheck H)
      ![leftOf (.projection 0),rightOf (.projection 0),rightOf (.projection 1)]
      (numeral 1) xs ![typ,raw,gamma] ht
    intro i
    exact Fin.cases (hv 0) (Fin.cases (hv 1) (Fin.cases (hv 2) (fun k => Fin.elim0 k))) i

theorem targetFieldsElim (H G : Program 1)
    (packed parameter typ raw c gamma : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (StepPair packed typ raw)))
    (hc : Nonempty (Derivation body Delta (StepPair parameter c gamma)))
    (ha : Nonempty (Derivation body Delta
      (graph2 (OriginalTypedDecoder.target H G) (numeral 1) packed parameter))) :
    Nonempty (Derivation body Delta
      (graph1 G (numeral 1) c ⊓
        OriginalTypedDecoderInternalAcceptance.TermAccepted H typ raw gamma)) := by
  let xs : Fin 2 → OTerm alpha := ![packed,parameter]
  have hv := fieldValues packed parameter typ raw c gamma hp hc
  have hh := conjunctionRecover _ _ xs ha
  apply andIntro
  · exact unaryRecover G (leftOf (.projection 1)) (numeral 1) c xs (andLeft hh) (hv 3)
  · apply compositionRecover (OriginalTypedDecoder.termCheck H)
      ![leftOf (.projection 0),rightOf (.projection 0),rightOf (.projection 1)]
      (numeral 1) xs ![typ,raw,gamma] (andRight hh)
    intro i
    exact Fin.cases (hv 0) (Fin.cases (hv 1) (Fin.cases (hv 2) (fun k => Fin.elim0 k))) i

theorem sourceFieldsIntro (H G : Program 1) (M W : Program 2)
    (packed parameter typ raw c gamma : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (StepPair packed typ raw)))
    (hc : Nonempty (Derivation body Delta (StepPair parameter c gamma)))
    (hg : Nonempty (Derivation body Delta (graph1 G (numeral 1) c)))
    (ht : Nonempty (Derivation body Delta
      (OriginalUniverseDecoderInternalAcceptance.TermAccepted H M W typ raw gamma c))) :
    Nonempty (Derivation body Delta
      (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) packed parameter)) := by
  let xs : Fin 2 → OTerm alpha := ![packed,parameter]
  have hv := fieldValues packed parameter typ raw c gamma hp hc
  apply conjunctionAccept _ _ xs
  · exact unaryValue G (leftOf (.projection 1)) (numeral 1) c xs hg (hv 3)
  · exact compositionValue (OriginalUniverseDecoder.termCheck H M W)
      ![leftOf (.projection 0),rightOf (.projection 0),rightOf (.projection 1),leftOf (.projection 1)]
      (numeral 1) xs ![typ,raw,gamma,c] ht hv

theorem sourceFieldsElim (H G : Program 1) (M W : Program 2)
    (packed parameter typ raw c gamma : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (StepPair packed typ raw)))
    (hc : Nonempty (Derivation body Delta (StepPair parameter c gamma)))
    (ha : Nonempty (Derivation body Delta
      (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) packed parameter))) :
    Nonempty (Derivation body Delta
      (graph1 G (numeral 1) c ⊓
        OriginalUniverseDecoderInternalAcceptance.TermAccepted H M W typ raw gamma c)) := by
  let xs : Fin 2 → OTerm alpha := ![packed,parameter]
  have hv := fieldValues packed parameter typ raw c gamma hp hc
  have hh := conjunctionRecover _ _ xs ha
  exact andIntro
    (unaryRecover G (leftOf (.projection 1)) (numeral 1) c xs (andLeft hh) (hv 3))
    (compositionRecover (OriginalUniverseDecoder.termCheck H M W)
      ![leftOf (.projection 0),rightOf (.projection 0),rightOf (.projection 1),leftOf (.projection 1)]
      (numeral 1) xs ![typ,raw,gamma,c] (andRight hh) hv)

theorem targetEquation (H G : Program 1)
    (packed parameter typ raw c gamma : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (StepPair packed typ raw)))
    (hc : Nonempty (Derivation body Delta (StepPair parameter c gamma))) :
    Nonempty (Derivation body Delta
      ((graph2 (OriginalTypedDecoder.target H G) (numeral 1) packed parameter).iff
        (graph1 G (numeral 1) c ⊓
          OriginalTypedDecoderInternalAcceptance.TermAccepted H typ raw gamma))) := by
  let P := graph2 (OriginalTypedDecoder.target H G) (numeral 1) packed parameter
  let Q := graph1 G (numeral 1) c ⊓ OriginalTypedDecoderInternalAcceptance.TermAccepted H typ raw gamma
  obtain ⟨hp⟩ := hp
  obtain ⟨hc⟩ := hc
  obtain ⟨hf⟩ := targetFieldsElim H G packed parameter typ raw c gamma
    ⟨addHyp hp P⟩ ⟨addHyp hc P⟩
    (show Nonempty (Derivation body (P :: Delta) P) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  have hq : Nonempty (Derivation body (Q :: Delta) Q) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := targetFieldsIntro H G packed parameter typ raw c gamma
    ⟨addHyp hp Q⟩ ⟨addHyp hc Q⟩ (andLeft hq) (andRight hq)
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

theorem sourceEquation (H G : Program 1) (M W : Program 2)
    (packed parameter typ raw c gamma : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (StepPair packed typ raw)))
    (hc : Nonempty (Derivation body Delta (StepPair parameter c gamma))) :
    Nonempty (Derivation body Delta
      ((graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) packed parameter).iff
        (graph1 G (numeral 1) c ⊓
          OriginalUniverseDecoderInternalAcceptance.TermAccepted H M W typ raw gamma c))) := by
  let P := graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) packed parameter
  let Q := graph1 G (numeral 1) c ⊓ OriginalUniverseDecoderInternalAcceptance.TermAccepted H M W typ raw gamma c
  obtain ⟨hp⟩ := hp
  obtain ⟨hc⟩ := hc
  obtain ⟨hf⟩ := sourceFieldsElim H G M W packed parameter typ raw c gamma
    ⟨addHyp hp P⟩ ⟨addHyp hc P⟩
    (show Nonempty (Derivation body (P :: Delta) P) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  have hq : Nonempty (Derivation body (Q :: Delta) Q) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := sourceFieldsIntro H G M W packed parameter typ raw c gamma
    ⟨addHyp hp Q⟩ ⟨addHyp hc Q⟩ (andLeft hq) (andRight hq)
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapsePackedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapsePackedProof
