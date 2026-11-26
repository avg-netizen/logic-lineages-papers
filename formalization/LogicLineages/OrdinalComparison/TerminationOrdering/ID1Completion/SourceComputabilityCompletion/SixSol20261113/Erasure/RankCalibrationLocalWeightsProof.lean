module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationChildWeightProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankArgumentLocalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapsePackedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationLocalWeightsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalTagArithmeticSyntaxProof (suc sucRelabel zRelabel)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open RankMemoDefinitions RankArgumentDefinitions RankCalibrationInductionSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
/-- Discharge the argument aggregator's LocalWeights from the actual original
context guard and strong child-code IH. No child rank/decoder relation is left
as a semantic premise. -/
theorem actualWeights (R : Program 2) (H G : Program 1) (M W : Program 2)
 (stage tab parameter gamma c : OTerm alpha)
 (ih : Nonempty (Derivation body Delta (RankCalibrationInductionDefinitions.BelowRaw R H G M W (suc stage))))
 (ht : Nonempty (Derivation body Delta (graph1 table tab stage)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (hg : Nonempty (Derivation body Delta (graph1 G (numeral 1) c))) :
 Nonempty (Derivation body Delta (LocalWeights (OriginalHereditaryEvaluatorDefinitions.evaluator R)
   lookupWeight H M W parameter gamma c (suc stage) (Fin.cons stage (Fin.cons tab Fin.elim0)))) := by
 unfold LocalWeights
 apply actualFiniteUniversalIntroduction body alpha 6 Delta
 let j : alpha → alpha ⊕ Fin 6 := Sum.inl
 let typ : OTerm (alpha ⊕ Fin 6) := .var (.inr 0)
 let raw : OTerm (alpha ⊕ Fin 6) := .var (.inr 1)
 let packed : OTerm (alpha ⊕ Fin 6) := .var (.inr 2)
 let child : OTerm (alpha ⊕ Fin 6) := .var (.inr 3)
 let typed : OTerm (alpha ⊕ Fin 6) := .var (.inr 4)
 let rank : OTerm (alpha ⊕ Fin 6) := .var (.inr 5)
 let A := OriginalUniverseDecoderInternalAcceptance.TermAccepted H M W typ raw (gamma.relabel j) (c.relabel j) ⊓
   (graph2 InternalPairing.pairing packed typ raw ⊓
   (graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) child packed (parameter.relabel j) ⊓
   (graph2 InternalPairing.pairing typed typ child ⊓
   (graph1 OriginalRawSyntaxTransport.variableRankRaw rank raw ⊓
    InternalLessThan.strictLess child (suc (stage.relabel j))))))
 let Theta := A :: Delta.map (fun f => f.relabel j)
 have inc : ∀ f ∈ Delta, f.relabel j ∈ Theta := fun f hf => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩)
 have ih' := renameInto ih j Theta inc
 have ht' := renameInto ht j Theta inc
 have hp' := renameInto hp j Theta inc
 have hg' := renameInto hg j Theta inc
 simp only [belowRawRename,graph1Rename,graph2Rename,sucRelabel,numeral,zRelabel] at ih' ht' hp' hg'
 have h : Nonempty (Derivation body Theta A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
 have hpair := andLeft (andRight h)
 have hs := OriginalTransparentDecoderValidatorCollapsePackedProof.sourceFieldsIntro H G M W
   packed (parameter.relabel j) typ raw (c.relabel j) (gamma.relabel j) hpair hp' hg' (andLeft h)
 have hr := OriginalRawVariableRankSupportProof.rankPackedBackward packed rank typ raw hpair
   (andLeft (andRight (andRight (andRight (andRight h)))))
 obtain ⟨out⟩ := RankCalibrationChildWeightProof.actualChildWeight R H G M W
   (stage.relabel j) (tab.relabel j) packed (parameter.relabel j) child rank typed typ ih' hs
   (andLeft (andRight (andRight h))) hr
   (andRight (andRight (andRight (andRight (andRight h))))) ht'
   (andLeft (andRight (andRight (andRight h))))
 have result := Nonempty.intro (Derivation.implicationIntroduction out)
 simpa only [weightMatrix,consTermRename,emptyRename,sucRelabel] using result
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationLocalWeightsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationLocalWeightsProof
