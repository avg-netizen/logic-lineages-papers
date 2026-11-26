module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapsePackedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceOutputBooleanProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapsePackedBooleanProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalControlGraphSupportProof
open OriginalHereditaryValidityInternalRecurrenceOutputBooleanProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Booleanity of the literal original target leaf, even for arbitrary H/G
and malformed packed values or contexts. -/
theorem targetBoolean (H G : Program 1) (out packed parameter : OTerm alpha)
    (ho : Nonempty (Derivation body Delta
      (graph2 (OriginalTypedDecoder.target H G) out packed parameter))) :
    Nonempty (Derivation body Delta
      (equal out (numeral 0) ⊔ equal out (numeral 1))) := by
  simpa only [equalEqn,numeral] using
    (conjunctionOutputBoolean
      (.composition G (fun _ : Fin 1 => leftOf (.projection 1)))
      (.composition (OriginalTypedDecoder.termCheck H)
        ![leftOf (.projection 0),rightOf (.projection 0),rightOf (.projection 1)])
      out ![packed,parameter] ho)

/-- Booleanity of the literal original source leaf does not assume Boolean
membership, head-window, context-guard, or head-signature programs. -/
theorem sourceBoolean (H G : Program 1) (M W : Program 2)
    (out packed parameter : OTerm alpha)
    (ho : Nonempty (Derivation body Delta
      (graph2 (OriginalUniverseDecoder.source H G M W) out packed parameter))) :
    Nonempty (Derivation body Delta
      (equal out (numeral 0) ⊔ equal out (numeral 1))) := by
  simpa only [equalEqn,numeral] using
    (conjunctionOutputBoolean
      (.composition G ![leftOf (.projection 1)])
      (.composition (OriginalUniverseDecoder.termCheck H M W)
        ![leftOf (.projection 0),rightOf (.projection 0),rightOf (.projection 1),leftOf (.projection 1)])
      out ![packed,parameter] ho)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapsePackedBooleanProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapsePackedBooleanProof
