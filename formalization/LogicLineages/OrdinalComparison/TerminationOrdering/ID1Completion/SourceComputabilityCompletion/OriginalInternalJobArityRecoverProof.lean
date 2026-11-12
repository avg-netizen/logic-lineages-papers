module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSubstitutionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobArityRecoverProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open OriginalRawSyntaxTransport OriginalLambdaTraversalInternalSubstitutionProof
open OriginalRawSyntaxTransportInternalConstructorSubstitutionProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem arityRecoverAt {n : Nat} (p : Program n) (arity raw : OTerm alpha) (xs : Fin n → OTerm alpha)
 (hp : Nonempty (Derivation body Delta (programGraph p raw xs)))
 (ha : Nonempty (Derivation body Delta (programGraph (arityOf p) arity xs))) :
 Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) arity raw)) := by
 apply (substitutionGraph (aritySubstitution (Substitutes.projection (gs := fun _ : Fin 1 => p) 0))
  (Fin.cons raw Fin.elim0) xs arity (fun i => ?_)).mpr ha
 obtain rfl := Fin.eq_zero i
 exact hp
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobArityRecoverProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobArityRecoverProof
