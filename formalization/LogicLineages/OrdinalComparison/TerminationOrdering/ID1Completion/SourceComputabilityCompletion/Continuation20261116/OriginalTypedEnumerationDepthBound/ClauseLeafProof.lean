module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.LeafDispatchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.GuardChoiceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.ClauseLeafProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open DispatchFrame
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {n : Nat} {H : Program 1} {arguments : Bool} {body : Positive (Fin 1)}
  {alpha : Type} {Delta : List (Formula alpha)}

theorem atVariable (f : Frame n H arguments body alpha Delta) (tag payload : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing f.raw tag payload))) :
    Nonempty (Derivation body Delta ((eqn tag (numeral 0)).imp f.conclusion)) := by
  let A := eqn tag (numeral 0)
  have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨d⟩ := LeafDispatchProof.variableCode (f.addHyp A) payload
    (OriginalEnumerationMembership.GuardPairProof.pairLiteral f.raw tag payload 0 (withHyp hp A) h)
  exact ⟨Derivation.implicationIntroduction d⟩

theorem atBottom (f : Frame n H arguments body alpha Delta) (tag payload : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing f.raw tag payload))) :
    Nonempty (Derivation body Delta ((eqn tag (numeral 3)).imp f.conclusion)) := by
  let A := eqn tag (numeral 3)
  have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨d⟩ := LeafDispatchProof.bottom (f.addHyp A) payload
    (OriginalEnumerationMembership.GuardPairProof.pairLiteral f.raw tag payload 3 (withHyp hp A) h)
  exact ⟨Derivation.implicationIntroduction d⟩

theorem atNil (f : Frame n H arguments body alpha Delta) (tag payload : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing f.raw tag payload))) :
    Nonempty (Derivation body Delta ((eqn tag (numeral 6) ⊓ eqn payload (numeral 0)).imp f.conclusion)) := by
  let A := eqn tag (numeral 6) ⊓ eqn payload (numeral 0)
  have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨d⟩ := LeafDispatchProof.nilCode (f.addHyp A) payload
    (OriginalEnumerationMembership.GuardPairProof.pairLiteral f.raw tag payload 6 (withHyp hp A) (andLeft h)) (andRight h)
  exact ⟨Derivation.implicationIntroduction d⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.ClauseLeafProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.ClauseLeafProof
