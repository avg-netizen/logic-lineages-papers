module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationInductionBindingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationInductionTransportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open InternalGraphComposition (OTerm)
open InternalTagArithmeticSyntaxProof (emb eqn)
open RankCalibrationInductionDefinitions RankCalibrationInductionSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem belowTransport (R : Program 2) (H G : Program 1) (M W : Program 2) (old new : OTerm alpha)
 (he : Nonempty (Derivation body Delta (eqn old new)))
 (h : Nonempty (Derivation body Delta (BelowRaw R H G M W old))) :
 Nonempty (Derivation body Delta (BelowRaw R H G M W new)) := by
 let theta : Formula (alpha ⊕ Fin 1) := InternalStrongInduction.below
   (InternalStrongInduction.lift (rawPredicate R H G M W (alpha := alpha))) (.var (.inr 0))
 obtain ⟨he⟩ := he
 obtain ⟨h⟩ := h
 have hi : Derivation body Delta (instantiate theta (emb old)) := by
   simpa only [theta,InternalStrongInductionSyntaxProof.belowInstantiate, BelowRaw] using h
 have out := Derivation.equalityElimination theta (emb old) (emb new) he hi
 simpa only [theta,InternalStrongInductionSyntaxProof.belowInstantiate, BelowRaw] using Nonempty.intro out

theorem atTransport (R : Program 2) (H G : Program 1) (M W : Program 2) (old new : OTerm alpha)
 (he : Nonempty (Derivation body Delta (eqn old new)))
 (h : Nonempty (Derivation body Delta (AtRaw R H G M W old))) :
 Nonempty (Derivation body Delta (AtRaw R H G M W new)) := by
 obtain ⟨he⟩ := he
 obtain ⟨h⟩ := h
 have hi : Derivation body Delta (instantiate (rawPredicate R H G M W) (emb old)) := by
   simpa only [rawPredicateInstantiate] using h
 have out := Derivation.equalityElimination (rawPredicate R H G M W) (emb old) (emb new) he hi
 simpa only [rawPredicateInstantiate] using Nonempty.intro out
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationInductionTransportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationInductionTransportProof
