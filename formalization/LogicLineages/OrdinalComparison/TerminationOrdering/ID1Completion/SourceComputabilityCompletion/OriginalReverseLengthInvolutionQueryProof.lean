module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalReverseLengthInvolutionCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalQuerySyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalReverseLengthInvolutionQueryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof hiding OTerm
open InternalTagArithmeticSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalTypedArgumentObservations (reverse)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
open OriginalReverseLengthInvolutionDefinitions OriginalReverseLengthInvolutionSyntaxProof OriginalReverseLengthInvolutionBindingProof OriginalReverseLengthInvolutionCoreProof

theorem atCons (raw head tail count mapped : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw raw)))
 (hf : Nonempty (Derivation body Delta (fields raw count mapped)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail))) :
 Nonempty (Derivation body Delta (outputs raw count mapped)) := by
 let l : Program 2 := .composition OriginalContextInsertion.length (fun _ : Fin 1 => .projection 1)
 let r : Program 2 := .composition reverse (fun _ : Fin 1 => .projection 1)
 let s : Program 2 := consOf (.projection 0) (OriginalRawSyntaxTransport.constant 2 0)
 let qs : Fin 3 → Program 2 := ![l,r,s]
 let xs : Fin 2 → OTerm alpha := ![head,tail]
 apply InternalApplicationStepPeelSupportProof.queryCases qs xs _
 intro beta rho ys Theta hrho hq
 let xx : Fin 2 → OTerm beta := ![head.relabel rho,tail.relabel rho]
 have hx : (fun i => (xs i).relabel rho) = xx := by
   funext i
   exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
 rw [hx] at hq
 simp only [outputs,conjunctionRename,graph1Rename]
 have hi' := renameInto hi rho Theta hrho
 rw [belowRawRename] at hi'
 have hf' := renameInto hf rho Theta hrho
 simp only [fields,conjunctionRename,graph1Rename] at hf'
 have hc' := renameInto hc rho Theta hrho
 rw [graph2Rename] at hc'
 have hl := unaryRecover OriginalContextInsertion.length (.projection 1) (ys 0) (tail.relabel rho) xx (hq 0) (projectionValue 1 xx)
 have hm := unaryRecover reverse (.projection 1) (ys 1) (tail.relabel rho) xx (hq 1) (projectionValue 1 xx)
 have hs := binaryRecover InternalListCodec.consCode (.projection 0) (OriginalRawSyntaxTransport.constant 2 0)
   (ys 2) (head.relabel rho) z xx (hq 2) (projectionValue 0 xx)
   (OriginalRawSyntaxTransportInternalVariableSupportProof.constantValue 0 xx)
 exact atThree (raw.relabel rho) (head.relabel rho) (tail.relabel rho) (count.relabel rho) (mapped.relabel rho)
   (ys 0) (ys 1) (ys 2) hi' hf' hc' hl hm hs

theorem atNonzero (raw count mapped : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw raw)))
 (hf : Nonempty (Derivation body Delta (fields raw count mapped)))
 (hne : Nonempty (Derivation body Delta (eqn raw z).not)) :
 Nonempty (Derivation body Delta (outputs raw count mapped)) := by
 apply OriginalContextInsertionLengthProof.nonzeroCases raw _ hne
 intro beta rho Theta head tail hrho hc
 simp only [outputs,conjunctionRename,graph1Rename]
 have hi' := renameInto hi rho Theta hrho
 rw [belowRawRename] at hi'
 have hf' := renameInto hf rho Theta hrho
 simp only [fields,conjunctionRename,graph1Rename] at hf'
 exact atCons (raw.relabel rho) head tail (count.relabel rho) (mapped.relabel rho) hi' hf' hc

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalReverseLengthInvolutionQueryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalReverseLengthInvolutionQueryProof
