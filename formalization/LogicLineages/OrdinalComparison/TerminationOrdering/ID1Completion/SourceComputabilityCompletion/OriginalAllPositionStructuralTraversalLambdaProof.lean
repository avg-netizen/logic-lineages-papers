module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionStructuralTraversalLambdaTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionStructuralTraversalSourceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyLambdaProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalOutputProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLambdaOutputProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionStructuralTraversalLambdaProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open UniformCertificateCompletion

open InternalApplicationCertificateConstructors
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalAllPositionStructuralTraversalDefinitions

theorem actualLambdaLaw : OriginalAllPositionStructuralTraversalLambdaTargets.ActualLambdaLaw := by
 intro p H G W P
 dsimp only
 intro body alpha Delta input out typ parameter mark d e child childParameter childOut value cutoff
   hRange hp hf hc hki hko
 let r := refined p H G W P
 have cp := OriginalLambdaTraversalLambdaOutputProof.childPremises r.base r.window
   input d e child typ parameter childParameter hf (andLeft hp) (andLeft (andRight hp))
 have childPremises := andIntro (andLeft cp) (andIntro (andRight cp) hc)
 have ci := OriginalLambdaTraversalOutputProof.invariantAtInput r.base r.window
   childOut child e childParameter childPremises
 have oi := OriginalLambdaTraversalOutputProof.invariantAtInput r.base r.window
   out input typ parameter hp
 have hctor := OriginalLambdaTraversalInternalLambdaProof.lambdaForward
   (OriginalLambdaTraversalSelection.leaf r.base r.window) input d e child parameter childParameter childOut out
   hf hc (andRight (andRight hp))
 have rebuilt := OriginalLambdaTraversalLambdaOutputProof.outputRebuild r.base r.window
   input out d e child childOut typ parameter childParameter hf (andLeft (andRight hp))
   (andIntro (andLeft ci) (andIntro (andLeft (andRight ci)) (andLeft (andRight (andRight ci))))) hctor
 have hfo := andRight (andRight (andRight rebuilt))
 have inputCtor := andRight (OriginalLambdaTraversalLambdaRootProof.sourceConstructor r.base r.window
   input d e child typ parameter childParameter hf (andRight (andLeft (andRight hp)))
   (andLeft (andLeft (andRight hp))))
 have hw := andLeft hp
 change Nonempty (Derivation body Delta (OriginalFunctionNeutrality.windowGraph (refined p H G W P).window input parameter)) at hw
 rw [OriginalAllPositionStructuralTraversalSourceProof.window] at hw
 exact OriginalPositionStructuralKeyLambdaProof.actualLambda p H G W body alpha Delta
   input out d e child childOut parameter childParameter cutoff value mark hRange hw
   (OriginalAllPositionStructuralTraversalSourceProof.sourceOfValidity p H G W P input parameter (andLeft (andLeft (andRight hp))))
   (OriginalAllPositionStructuralTraversalSourceProof.sourceOfValidity p H G W P out parameter (andLeft oi))
   (OriginalAllPositionStructuralTraversalSourceProof.sourceOfValidity p H G W P child childParameter (andLeft (andRight cp)))
   (OriginalAllPositionStructuralTraversalSourceProof.sourceOfValidity p H G W P childOut childParameter (andLeft ci))
   hf hfo inputCtor hctor hki hko

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionStructuralTraversalLambdaProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionStructuralTraversalLambdaProof
