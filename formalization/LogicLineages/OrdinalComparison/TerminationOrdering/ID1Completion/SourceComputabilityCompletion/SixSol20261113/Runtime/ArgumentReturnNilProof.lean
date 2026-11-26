module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildConsQueriesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportRejectedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.PrefixFrameIdentityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ArgumentReturnNilProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedSourceSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
open OriginalInternalJobAdmissible OriginalUniverseDecoderInternalAcceptance
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalTagArithmeticSupportProof (refl)
theorem witnessAtNil (H : Program 1) (M W : Program 2) (raw gamma c payload : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (Admissible H M W (numeral 1) (numeral 0) raw gamma c)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 6) payload))) :
 Nonempty (Derivation body Delta (ArgumentsWitness H M W raw gamma c)) := by
 let A := equal (numeral 1) (numeral 0) ⊓ TermAccepted H M W (numeral 0) raw gamma c
 let B := equal (numeral 1) (numeral 1) ⊓ (equal (numeral 0) (numeral 0) ⊓ ArgumentsWitness H M W raw gamma c)
 apply OriginalTypedDecoderInternalBranchProof.orCases ha
 · have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
   exact OriginalUniverseDecoderTransportRejectedProof.termSix H M W raw payload (numeral 0) gamma c _ (withHyp hp A) (andRight h)
 · have h : Nonempty (Derivation body (B :: Delta) B) := ⟨Derivation.hypothesis List.mem_cons_self⟩
   exact andRight (andRight h)
theorem constructor (H : Program 1) (M W : Program 2) (raw gamma c payload : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (Admissible H M W (numeral 1) (numeral 0) raw gamma c)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 6) payload))) :
 Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.nilConstructor raw Fin.elim0)) := by
 apply OriginalInternalJobChildConsQueriesProof.argumentsCases H M W raw gamma c _ (witnessAtNil H M W raw gamma c payload ha hp)
 intro beta j Theta types hi htypes
 have hp' := renameInto hp j Theta hi
 simp only [graph2Rename,numeralRename] at hp'
 have hi := OriginalUniverseDecoderInternalAcceptanceLeafProof.nilIff H M W (raw.relabel j) (payload.relabel j) types (gamma.relabel j) (c.relabel j) hp'
 have hforward := andLeft hi
 obtain ⟨hf⟩ := hforward
 obtain ⟨ht⟩ := htypes
 have hparts : Nonempty (Derivation body Theta (equal (payload.relabel j) (numeral 0) ⊓ equal types (numeral 0))) :=
   ⟨Derivation.implicationElimination hf ht⟩
 have he : Nonempty (Derivation body Theta (InternalTagArithmeticSyntaxProof.eqn (payload.relabel j) (numeral 0))) := by
   simpa only [equalEqn] using andLeft hparts
 have hnil := PrefixFrameIdentityProof.binaryInputs InternalPairing.pairing (raw.relabel j) (numeral 6) (payload.relabel j) (numeral 6) (numeral 0) ⟨refl (numeral 6)⟩ he hp'
 simp only [programRename,emptyRename]
 exact binaryValue InternalPairing.pairing (OriginalRawSyntaxTransport.constant 0 6) (OriginalRawSyntaxTransport.constant 0 0)
   (raw.relabel j) (numeral 6) (numeral 0) Fin.elim0 hnil
   (OriginalRawSyntaxTransportInternalVariableSupportProof.constantValue 6 Fin.elim0)
   (OriginalRawSyntaxTransportInternalVariableSupportProof.constantValue 0 Fin.elim0)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ArgumentReturnNilProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ArgumentReturnNilProof
