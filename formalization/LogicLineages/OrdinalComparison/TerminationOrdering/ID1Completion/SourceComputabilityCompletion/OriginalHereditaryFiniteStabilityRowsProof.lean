module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryFiniteStabilityTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryObservationSourceRowsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryNativeBoundSliceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryFiniteStabilityRowsProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedLeastCodeRepresentative NumberedMultisetNumeric
open OriginalHereditaryNativeBoundDefinitions OriginalHereditaryFiniteStability OriginalHereditaryDeletionRows

theorem prefixDependency (Q T : Program 2) (n : Nat) (arity : Fin n → Nat) (c : Nat)
 (binders tail : List Ty) (sigma : Ty) (q : Packed (Fin n) arity (binders ++ sigma :: tail))
 (h : StepAgreement Q T c ⟨binders ++ sigma :: tail,q⟩) :
 evaluate (observation Q) (List.Vector.ofFn ![binders.length,packedNumber q,Nat.pair c (typesNumber (binders ++ sigma::tail))]) =
 evaluate (observation T) (List.Vector.ofFn ![binders.length,packedNumber q,Nat.pair c (typesNumber (binders ++ sigma::tail))]) := by
 rw [← OriginalTypedDecoderReconstructionLocalProof.contextNumber,
   OriginalHereditaryDeletionRowsNativeProof.observationPrefix,
   OriginalHereditaryDeletionRowsNativeProof.observationPrefix,
   OriginalClassContextPrefixNativeProof.erasedPackedOnTyped,
   OriginalClassContextPrefixNativeProof.erasedPackedOnTyped,
   OriginalTypedDecoderReconstructionLocalProof.contextNumber]
 exact h _ (OriginalHereditaryNativeBoundSliceProof.prefixDeletionStep n arity binders tail sigma q.1 q.2)

theorem rowsDependency (Q T : Program 2) (n : Nat) (arity : Fin n → Nat) (c : Nat)
 (s : State (Fin n) arity) (h : StepAgreement Q T c s) :
 value (rows Q) c s = value (rows T) c s := by
 rcases s with ⟨Gamma,q⟩
 simp only [value,OriginalHereditaryDeletionRowsBoundProof.nativeRows,Nat.unpair_pair,
   OriginalHereditaryObservationSourceRowsProof.lengthAtContext]
 apply congrArg numbersNumber
 unfold values
 apply List.map_congr_left
 intro k hk
 obtain ⟨binders,tail,sigma,he,hl⟩ := OriginalHereditaryObservationSourceRowsProof.prefixAt Gamma k (List.mem_range.mp hk)
 cases he
 rw [← hl]
 exact prefixDependency Q T n arity c binders tail sigma q h
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryFiniteStabilityRowsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryFiniteStabilityRowsProof
