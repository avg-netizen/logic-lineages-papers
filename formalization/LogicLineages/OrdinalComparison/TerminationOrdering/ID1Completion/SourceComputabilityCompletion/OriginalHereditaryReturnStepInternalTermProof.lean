module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnStepInternalSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformVertexPathSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnStepInternalTermProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open OriginalRawSyntaxTransportInternalConstructorSupportProof (numeralNe)
open OriginalTypedDecoderInternalBranchProof (sameYesIntro sameNoIntro)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
open OriginalHereditaryReturnStepInternalSupportProof
open InternalOriginalUniformVertexPathSupportProof (ternaryValue)

theorem termLaw : OriginalHereditaryReturnStepInternalTargets.TermLaw := by
 intro R body alpha Delta input work results frame rest payload packed parameter first second row old root returned tail value stack out
   hstate hwork hframe hrole hpacked hparameter hfirst hsecond hrow hold hroot hreturned htail hvalue hstack hout
 let xs : Fin 1 → OTerm alpha := ![input]
 have hr : Nonempty (Derivation body Delta (graph1
   (.composition (OriginalRootObservation.rootObservation R) ![OriginalHereditaryReturnStep.packed,OriginalHereditaryReturnStep.parameter]) root input)) :=
   binaryValue (OriginalRootObservation.rootObservation R) OriginalHereditaryReturnStep.packed
     OriginalHereditaryReturnStep.parameter root packed parameter xs hroot hpacked hparameter
 have hv : Nonempty (Derivation body Delta (graph1
   (.composition OriginalHereditaryReturn.returnRoot ![OriginalHereditaryReturnStep.packed,OriginalHereditaryReturnStep.firstSlot,OriginalHereditaryReturnStep.secondSlot]) returned input)) :=
   ternaryValue OriginalHereditaryReturn.returnRoot OriginalHereditaryReturnStep.packed
     OriginalHereditaryReturnStep.firstSlot OriginalHereditaryReturnStep.secondSlot returned packed first second xs hreturned hpacked hfirst hsecond
 have ht := binaryValue InternalPairing.pairing
   (.composition OriginalHereditaryReturn.returnRoot ![OriginalHereditaryReturnStep.packed,OriginalHereditaryReturnStep.firstSlot,OriginalHereditaryReturnStep.secondSlot])
   OriginalHereditaryReturnStep.deletionRow tail returned row xs htail hv hrow
 have hall : Nonempty (Derivation body Delta (graph1 (OriginalHereditaryReturnStep.termValue R) value input)) :=
   binaryValue InternalPairing.pairing _ _ value root tail xs hvalue hr ht
 have hp := popGraph (OriginalHereditaryReturnStep.termValue R) input rest value old stack out
   (restGraph input work results frame rest hstate hwork) hall hold hstack hout
 exact control R input work results frame rest payload out hstate hwork hframe (termRole R input out hrole hp)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnStepInternalTermProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnStepInternalTermProof
