module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyTypedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityParameterProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyRawProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedLeastCodeRepresentative NumberedMultisetNumeric
open NumberedFiniteUniverse NumberedNumericCarrier NumberedNumericDecoding
open OriginalHereditaryEvaluatorDefinitions
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem sourceWitness (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty) (value : Nat)
 (hs : InternalOriginalStepGuard.sourceValidityValue n arity symbols S Gamma value = 1) :
 ∃ q : Packed (Fin n) arity Gamma, packedNumber q = value ∧ InUniverse symbols S q.2 := by
 cases hd : decodeUniverse n arity symbols S Gamma value with
 | none => simp [InternalOriginalStepGuard.sourceValidityValue,rawCarrierTest,hd] at hs
 | some q => exact ⟨q,(NumberedNumericCarrierProof.numericUniverseDecode n arity symbols S Gamma value q).mp hd⟩

/-- Raw numeric slice theorem with genuine source witnesses and original
parameter codec. Used only for native class-test calibration. -/
theorem rawKeyIff (n : Nat) (arity : Fin n → Nat)
 (data : InternalOriginalUniformDescentSelection.Data)
 (hc : InternalOriginalUniformDescentSelection.Calibrated n arity data)
 (parameter seed candidate : Nat) (ctx : OrdinaryArithmeticQuotient.Context n) (Gamma : List Ty)
 (hctx : Encodable.decode (Nat.unpair parameter).1 = some ctx)
 (hclosed : SubtypeClosed (fun t => t ∈ ctx.1.2))
 (hg : Encodable.encode Gamma = (Nat.unpair parameter).2)
 (hs : InternalOriginalStepGuard.sourceValidityValue n arity ctx.1.1 ctx.1.2 Gamma seed = 1)
 (ht : InternalOriginalStepGuard.sourceValidityValue n arity ctx.1.1 ctx.1.2 Gamma candidate = 1) :
 (evaluate (evaluator data.oldRepresentative) (List.Vector.ofFn ![seed,parameter]) =
  evaluate (evaluator data.oldRepresentative) (List.Vector.ofFn ![candidate,parameter])) ↔
 (evaluate data.oldRepresentative (List.Vector.ofFn ![seed,parameter]) =
  evaluate data.oldRepresentative (List.Vector.ofFn ![candidate,parameter])) := by
 obtain ⟨q,hq,hqu⟩ := sourceWitness n arity ctx.1.1 ctx.1.2 Gamma seed hs
 obtain ⟨r,hr,hru⟩ := sourceWitness n arity ctx.1.1 ctx.1.2 Gamma candidate ht
 have hgamma : typesNumber Gamma = (Nat.unpair parameter).2 :=
   (OriginalTypedDecoderReconstructionLocalProof.contextNumber Gamma).symm.trans hg
 have hp : Nat.pair (Nat.unpair parameter).1 (typesNumber Gamma) = parameter := by
   rw [hgamma,Nat.pair_unpair]
 have he := EvaluatorKeyTypedProof.typedKeyIff n arity data hc (Nat.unpair parameter).1 ctx hctx hclosed Gamma q r hqu hru
 simpa only [hq,hr,hp] using he
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyRawProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyRawProof
