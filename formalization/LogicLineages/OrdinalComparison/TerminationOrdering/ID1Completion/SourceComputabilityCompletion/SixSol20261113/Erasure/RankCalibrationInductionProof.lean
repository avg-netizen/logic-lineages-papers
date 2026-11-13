module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationBranchesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationInductionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open RankCalibrationInductionDefinitions RankCalibrationInductionSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem actualStep (R : Program 2) (H G : Program 1) (M W : Program 2) (code : OTerm alpha)
 (ih : Nonempty (Derivation body Delta (BelowRaw R H G M W code))) :
 Nonempty (Derivation body Delta (AtRaw R H G M W code)) := by
 apply RankCalibrationInductionBindingProof.atRawIntro R H G M W code
 let j : alpha → alpha ⊕ Fin 3 := Sum.inl
 let input : OTerm (alpha ⊕ Fin 3) := .var (.inr 0)
 let parameter : OTerm (alpha ⊕ Fin 3) := .var (.inr 1)
 let rank : OTerm (alpha ⊕ Fin 3) := .var (.inr 2)
 let A := fields R H G M W (code.relabel j) input parameter rank
 let Theta := A :: Delta.map (fun f => f.relabel j)
 have inc : ∀ f ∈ Delta, f.relabel j ∈ Theta := fun f hf => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩)
 have ih' := renameInto ih j Theta inc
 rw [belowRawRename] at ih'
 have h : Nonempty (Derivation body Theta A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
 obtain ⟨out⟩ := RankCalibrationBranchesProof.actualAt R H G M W (code.relabel j) input parameter rank
   ih' (andLeft h) (andLeft (andRight h)) (andRight (andRight h))
 exact ⟨Derivation.implicationIntroduction out⟩

theorem actualAtRaw (R : Program 2) (H G : Program 1) (M W : Program 2) (code : OTerm alpha) :
 Nonempty (Derivation body Delta (AtRaw R H G M W code)) :=
 RankCalibrationInductionBindingProof.rawInduction R H G M W code
   (fun _ _ c ih => actualStep R H G M W c ih)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationInductionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationInductionProof
