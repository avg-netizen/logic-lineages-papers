module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorInductionBindingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorInductionTransportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open InternalGraphComposition (OTerm)
open InternalTagArithmeticSyntaxProof (emb eqn)
open EvaluatorConstructorInductionDefinitions EvaluatorConstructorInductionSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem belowTransport (R : Program 2) (H G : Program 1) (M W : Program 2) (old new : OTerm alpha)
 (he : Nonempty (Derivation body Delta (eqn old new)))
 (h : Nonempty (Derivation body Delta (BelowLength R H G M W old))) :
 Nonempty (Derivation body Delta (BelowLength R H G M W new)) := by
 let theta : Formula (alpha ⊕ Fin 1) := InternalStrongInduction.below
   (InternalStrongInduction.lift (predicate R H G M W (alpha := alpha))) (.var (.inr 0))
 obtain ⟨he⟩ := he
 obtain ⟨h⟩ := h
 have hi : Derivation body Delta (instantiate theta (emb old)) := by
   simpa only [theta,InternalStrongInductionSyntaxProof.belowInstantiate, BelowLength] using h
 have out := Derivation.equalityElimination theta (emb old) (emb new) he hi
 simpa only [theta,InternalStrongInductionSyntaxProof.belowInstantiate, BelowLength] using Nonempty.intro out

theorem atTransport (R : Program 2) (H G : Program 1) (M W : Program 2) (old new : OTerm alpha)
 (he : Nonempty (Derivation body Delta (eqn old new)))
 (h : Nonempty (Derivation body Delta (AtLength R H G M W old))) :
 Nonempty (Derivation body Delta (AtLength R H G M W new)) := by
 obtain ⟨he⟩ := he
 obtain ⟨h⟩ := h
 have hi : Derivation body Delta (instantiate (predicate R H G M W) (emb old)) := by
   simpa only [predicateInstantiate] using h
 have out := Derivation.equalityElimination (predicate R H G M W) (emb old) (emb new) he hi
 simpa only [predicateInstantiate] using Nonempty.intro out
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorInductionTransportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorInductionTransportProof
