module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankArgumentCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankArgumentNilProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.SpineCasesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankArgumentProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open RankArgumentDefinitions RankArgumentInductionDefinitions RankArgumentInductionSyntax
open RankArgumentInductionBinding RankArgumentCoreProof SortWeightedDefinitions
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)} {k : Nat}
variable (Q : Program 2) (F : Program (k+1)) (H : Program 1) (M W : Program 2)
attribute [local irreducible] programGraph
theorem fromFields (parameter gamma c bound raw types observations rank : OTerm alpha)
 (params : Fin k → OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw Q F H M W parameter gamma c bound raw params)))
 (hw : Nonempty (Derivation body Delta (LocalWeights Q F H M W parameter gamma c bound params)))
 (hf : Nonempty (Derivation body Delta (fields Q H M W parameter gamma c bound raw types observations rank))) :
 Nonempty (Derivation body Delta (programGraph (weighted F) rank (Fin.cons observations params))) := by
 apply Context.SpineCasesProof.actualCases H M W body alpha Delta types raw gamma c _ (andLeft hf)
 · intro beta j Theta hj hn
   simp only [programRename,consTermRename]
   have hf' := renameInto hf j Theta hj
   rw [fieldsRename] at hf'
   exact RankArgumentNilProof.nilResult Q F (raw.relabel j) (parameter.relabel j)
     (observations.relabel j) (rank.relabel j) (fun i => (params i).relabel j) hn
     (andLeft (andRight hf')) (andLeft (andRight (andRight hf')))
 · intro beta j Theta typ child tail requested tailTypes hj hc _ hh ht hlt
   simp only [programRename,consTermRename]
   have hi' := renameInto hi j Theta hj
   rw [belowRawRename] at hi'
   have hw' := renameInto hw j Theta hj
   rw [RankArgumentSyntax.weightsRename] at hw'
   have hf' := renameInto hf j Theta hj
   rw [fieldsRename] at hf'
   exact consQuery Q F H M W (parameter.relabel j) (gamma.relabel j) (c.relabel j)
     (bound.relabel j) (raw.relabel j) (types.relabel j) (observations.relabel j) (rank.relabel j)
     typ child tail tailTypes (fun i => (params i).relabel j) hi' hw' hf' hc hh ht hlt

theorem atRawFrom (parameter gamma c bound raw : OTerm alpha) (params : Fin k → OTerm alpha)
 (hw : Nonempty (Derivation body Delta (LocalWeights Q F H M W parameter gamma c bound params)))
 (hi : Nonempty (Derivation body Delta (BelowRaw Q F H M W parameter gamma c bound raw params))) :
 Nonempty (Derivation body Delta (AtRaw Q F H M W parameter gamma c bound raw params)) := by
 let j : alpha → alpha ⊕ Fin 3 := Sum.inl
 let types : OTerm (alpha ⊕ Fin 3) := .var (.inr 0)
 let observations : OTerm (alpha ⊕ Fin 3) := .var (.inr 1)
 let rank : OTerm (alpha ⊕ Fin 3) := .var (.inr 2)
 let A := fields Q H M W (parameter.relabel j) (gamma.relabel j) (c.relabel j)
   (bound.relabel j) (raw.relabel j) types observations rank
 let Theta := A :: Delta.map (fun q => q.relabel j)
 have inc : ∀ q ∈ Delta, q.relabel j ∈ Theta := by
   intro q hq; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩)
 have hi' := renameInto hi j Theta inc
 rw [belowRawRename] at hi'
 have hw' := renameInto hw j Theta inc
 rw [RankArgumentSyntax.weightsRename] at hw'
 obtain ⟨out⟩ := fromFields Q F H M W (parameter.relabel j) (gamma.relabel j) (c.relabel j)
   (bound.relabel j) (raw.relabel j) types observations rank (fun i => (params i).relabel j)
   hi' hw' (show Nonempty (Derivation body Theta A) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
 exact InternalClosedProgramsBindingProof.introduction body alpha 3 Delta _
   ⟨Derivation.implicationIntroduction out⟩

theorem actualAtRaw : RankArgumentInductionTargets.ActualAtRaw := by
 intro k Q F H M W body alpha Delta parameter gamma c bound raw params hw
 exact rawInduction Q F H M W parameter gamma c bound raw params hw
   (fun _ _ p g ctx b r ps weights below => atRawFrom Q F H M W p g ctx b r ps weights below)

theorem actualAggregation : RankArgumentTargets.ActualAggregation := by
 intro k Q F H M W body alpha Delta types raw parameter gamma c observations rank bound params ha _ hp hr hs hw
 exact atRawApply Q F H M W parameter gamma c bound raw types observations rank params
   (actualAtRaw k Q F H M W body alpha Delta parameter gamma c bound raw params hw)
   (andIntro ha (andIntro hp (andIntro hr hs)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankArgumentProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankArgumentProof
