module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationExtensionalCallProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalBranchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalPairingOrderArithmeticProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationExtensionalBranchProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof
open SourceComputabilityFormulaSupportProof (numeral)
open InternalOriginalPairingOrderArithmeticProof (formulaCases withHyp)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open OriginalTypedDecoderInternalBranchProof (sameYesIntro sameYesElim sameNoIntro sameNoElim)
open OriginalTypedArgumentObservationsCongruence OriginalTypedArgumentObservationsCongruenceSyntaxProof
open OriginalTypedArgumentObservationsAccumulatorQueryProof OriginalTypedArgumentObservationsCongruenceAgreementProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem branchForward (X F G U V : Program 2) (k : Nat) (parameter input out : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (Agreement F G parameter)))
 (hu : Nonempty (Derivation body Delta (Agreement U V parameter)))
 (ho : Nonempty (Derivation body Delta (graph2 (OriginalTypedDecoder.ifSame X (OriginalRawSyntaxTransport.constant 2 k) F U) out input parameter))) :
 Nonempty (Derivation body Delta (graph2 (OriginalTypedDecoder.ifSame X (OriginalRawSyntaxTransport.constant 2 k) G V) out input parameter)) := by
 apply binaryCases X input parameter _
 intro beta rho Theta control hrho ht
 rw [graph2Rename]
 have hf' := renameInto hf rho Theta hrho
 have hu' := renameInto hu rho Theta hrho
 rw [agreementRename] at hf' hu'
 have ho' := renameInto ho rho Theta hrho
 rw [graph2Rename] at ho'
 let xs : Fin 2 → OTerm beta := ![input.relabel rho,parameter.relabel rho]
 have hn := constantValue (body := body) (Delta := Theta) k xs
 let E := equal control (numeral k)
 apply formulaCases E _
 · have he : Nonempty (Derivation body (E :: Theta) E) := ⟨Derivation.hypothesis List.mem_cons_self⟩
   have hr := sameYesElim X (OriginalRawSyntaxTransport.constant 2 k) F U (out.relabel rho) control (numeral k) xs
     (withHyp ht E) (withHyp hn E) he (withHyp ho' E)
   have hs := agreementForward F G (parameter.relabel rho) (input.relabel rho) (out.relabel rho) (withHyp hf' E) hr
   exact sameYesIntro X (OriginalRawSyntaxTransport.constant 2 k) G V (out.relabel rho) control (numeral k) xs
     (withHyp ht E) (withHyp hn E) he hs
 · have he : Nonempty (Derivation body (E.not :: Theta) E.not) := ⟨Derivation.hypothesis List.mem_cons_self⟩
   have hr := sameNoElim X (OriginalRawSyntaxTransport.constant 2 k) F U (out.relabel rho) control (numeral k) xs
     (withHyp ht E.not) (withHyp hn E.not) he (withHyp ho' E.not)
   have hs := agreementForward U V (parameter.relabel rho) (input.relabel rho) (out.relabel rho) (withHyp hu' E.not) hr
   exact sameNoIntro X (OriginalRawSyntaxTransport.constant 2 k) G V (out.relabel rho) control (numeral k) xs
     (withHyp ht E.not) (withHyp hn E.not) he hs

theorem branchAgreement (X F G U V : Program 2) (k : Nat) (parameter : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (Agreement F G parameter)))
 (hu : Nonempty (Derivation body Delta (Agreement U V parameter))) :
 Nonempty (Derivation body Delta (Agreement
   (OriginalTypedDecoder.ifSame X (OriginalRawSyntaxTransport.constant 2 k) F U)
   (OriginalTypedDecoder.ifSame X (OriginalRawSyntaxTransport.constant 2 k) G V) parameter)) := by
 apply agreementIntro _ _ parameter
 intro beta rho Theta input left right hrho hl hr
 have hf' := renameInto hf rho Theta hrho
 have hu' := renameInto hu rho Theta hrho
 rw [agreementRename] at hf' hu'
 have hs := branchForward X F G U V k (parameter.relabel rho) input left hf' hu' hl
 simpa only [equalEqn] using valueUnique
   (OriginalTypedDecoder.ifSame X (OriginalRawSyntaxTransport.constant 2 k) G V) left right ![input,parameter.relabel rho] hs hr
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationExtensionalBranchProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationExtensionalBranchProof
