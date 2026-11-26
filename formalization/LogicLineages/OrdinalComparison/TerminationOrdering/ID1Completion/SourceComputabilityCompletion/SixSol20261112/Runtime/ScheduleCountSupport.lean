module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.ScheduleCountTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobArityRecoverProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalMultiplicationLawsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.ScheduleCountSupport
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (eqn z suc)
open InternalTagArithmeticSupportProof
open InternalAdditionLawsProof (add leftZero leftSuccessor)
open InternalMultiplicationLawsProof (congAddRight)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport
open OriginalLambdaTraversalInternalSubstitutionProof
open OriginalRawSyntaxTransportInternalConstructorSubstitutionProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
/-- The original syntactic substitution theorem, used in the forward
direction to observe the SAME raw arity in the two-input child scheduler. -/
theorem arityAt {n : Nat} (p : Program n) (arity raw : OTerm alpha) (xs : Fin n → OTerm alpha)
 (hp : Nonempty (Derivation body Delta (programGraph p raw xs)))
 (ha : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) arity raw))) :
 Nonempty (Derivation body Delta (programGraph (arityOf p) arity xs)) := by
 apply (substitutionGraph
   (aritySubstitution (Substitutes.projection (gs := fun _ : Fin 1 => p) 0))
   (Fin.cons raw Fin.elim0) xs arity (fun i => ?_)).mp ha
 obtain rfl := Fin.eq_zero i
 exact hp
theorem sumZero (arity count : OTerm alpha)
 (he : Nonempty (Derivation body Delta (eqn arity (numeral 0)))) :
 Nonempty (Derivation body Delta (eqn (add arity count) count)) := by
 obtain ⟨he⟩ := he
 have hz : Derivation body Delta (eqn arity z) := by simpa only [numeral] using he
 exact ⟨trans (congAddRight count hz) (leftZero count)⟩
theorem sumOne (arity count : OTerm alpha)
 (he : Nonempty (Derivation body Delta (eqn arity (numeral 1)))) :
 Nonempty (Derivation body Delta (eqn (add arity count) (suc count))) := by
 obtain ⟨he⟩ := he
 have h1 : Derivation body Delta (eqn arity (suc z)) := by simpa only [numeral] using he
 exact ⟨trans (congAddRight count h1)
   (trans (leftSuccessor z count) (congSuc (leftZero count)))⟩
theorem sumTwo (arity count : OTerm alpha)
 (he : Nonempty (Derivation body Delta (eqn arity (numeral 2)))) :
 Nonempty (Derivation body Delta (eqn (add arity count) (suc (suc count)))) := by
 obtain ⟨he⟩ := he
 have h2 : Derivation body Delta (eqn arity (suc (suc z))) := by simpa only [numeral] using he
 exact ⟨trans (congAddRight count h2)
   (trans (leftSuccessor (suc z) count)
     (congSuc (trans (leftSuccessor z count) (congSuc (leftZero count)))))⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.ScheduleCountSupport
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.ScheduleCountSupport
