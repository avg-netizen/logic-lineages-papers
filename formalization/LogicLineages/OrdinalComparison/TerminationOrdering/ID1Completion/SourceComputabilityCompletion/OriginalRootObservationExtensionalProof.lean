module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationExtensionalValuesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationExtensionalBranchProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationExtensionalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalTypedArgumentObservationsCongruence OriginalTypedArgumentObservationsCongruenceAgreementProof
open OriginalRootObservationExtensional OriginalRootObservationExtensionalValuesProof OriginalRootObservationExtensionalBranchProof
open OriginalRootObservation
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem rootAgreement (R S : Program 2) (param : OTerm alpha)
 (hg : Nonempty (Derivation body Delta (GlobalAgreement R S))) :
 Nonempty (Derivation body Delta (Agreement (rootObservation R) (rootObservation S) param)) := by
 have h6 := agreementRefl (body := body) (Delta := Delta) (OriginalRawSyntaxTransport.constant 2 0) param
 have h5 := branchAgreement tag (numbered R) (numbered S) (OriginalRawSyntaxTransport.constant 2 0) (OriginalRawSyntaxTransport.constant 2 0) 5 param
   (numberedAgreement R S param hg) h6
 have h4 := branchAgreement tag (ordinary R) (ordinary S) (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 5) (numbered R) (OriginalRawSyntaxTransport.constant 2 0)) (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 5) (numbered S) (OriginalRawSyntaxTransport.constant 2 0)) 4 param
   (ordinaryAgreement R S param hg) h5
 have h3 := branchAgreement tag bottom bottom (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 4) (ordinary R) (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 5) (numbered R) (OriginalRawSyntaxTransport.constant 2 0))) (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 4) (ordinary S) (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 5) (numbered S) (OriginalRawSyntaxTransport.constant 2 0))) 3 param
   (agreementRefl bottom param) h4
 have h2 := branchAgreement tag (application R) (application S) (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 3) bottom (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 4) (ordinary R) (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 5) (numbered R) (OriginalRawSyntaxTransport.constant 2 0)))) (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 3) bottom (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 4) (ordinary S) (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 5) (numbered S) (OriginalRawSyntaxTransport.constant 2 0)))) 2 param
   (applicationAgreement R S param hg) h3
 have h1 := branchAgreement tag (lambda R) (lambda S) (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 2) (application R) (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 3) bottom (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 4) (ordinary R) (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 5) (numbered R) (OriginalRawSyntaxTransport.constant 2 0))))) (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 2) (application S) (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 3) bottom (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 4) (ordinary S) (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 5) (numbered S) (OriginalRawSyntaxTransport.constant 2 0))))) 1 param
   (lambdaAgreement R S param hg) h2
 have h0 := branchAgreement tag variableCase variableCase (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 1) (lambda R) (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 2) (application R) (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 3) bottom (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 4) (ordinary R) (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 5) (numbered R) (OriginalRawSyntaxTransport.constant 2 0)))))) (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 1) (lambda S) (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 2) (application S) (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 3) bottom (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 4) (ordinary S) (OriginalTypedDecoder.ifSame tag (OriginalRawSyntaxTransport.constant 2 5) (numbered S) (OriginalRawSyntaxTransport.constant 2 0)))))) 0 param
   (agreementRefl variableCase param) h1
 exact h0

theorem exactExtensionality : OriginalRootObservationExtensionalTargets.RootExtensionality := by
 intro R S body alpha Delta parameter
 let A : Formula alpha := GlobalAgreement R S
 obtain ⟨h⟩ := rootAgreement R S parameter (body := body) (Delta := A :: Delta) ⟨Derivation.hypothesis List.mem_cons_self⟩
 exact ⟨Derivation.implicationIntroduction h⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationExtensionalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationExtensionalProof
