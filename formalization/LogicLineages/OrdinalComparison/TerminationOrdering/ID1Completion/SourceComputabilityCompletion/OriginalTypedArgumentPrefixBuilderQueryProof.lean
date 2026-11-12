module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentPrefixBuilderCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsInternalConsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListMapProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformVertexPathSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairReverseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendListProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentPrefixBuilderQueryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionClosureLogicProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z eqn)
open InternalTagArithmeticSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalOriginalUniformVertexPathSupportProof (ternaryValue ternaryRecover)
open OriginalTypedArgumentPrefixBuilderCoreProof OriginalTypedArgumentPrefixBuilderSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalTypedArgumentPrefixBuilder OriginalTypedArgumentPrefixBuilderRowDefinitions OriginalTypedArgumentPrefixBuilderBindingProof OriginalTypedArgumentObservations
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem consCore (R : Program 2) (raw head tail suffix built parameter mappedValue suffixValue total : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw R raw)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
 (hf : Nonempty (Derivation body Delta (fields R raw suffix built parameter mappedValue suffixValue total))) :
 Nonempty (Derivation body Delta (graph2 (argumentObservations R) total built parameter)) := by
 let ty : Program 5 := leftOf (.projection 0)
 let ch : Program 5 := rightOf (.projection 0)
 let ob : Program 5 := .composition R ![.projection 0,.projection 3]
 let typedHead : Program 5 := pairOf ty ob
 let bu : Program 5 := .composition build ![.projection 1,.projection 2]
 let ma : Program 5 := .composition (mapped R) ![.projection 1,.projection 3]
 let ap : Program 5 := .composition InternalApplicationValidityStackAppend.append ![ma,.projection 4]
 let ca : Program 5 := .composition OriginalRawSyntaxTransport.consConstructor ![ty,ch,bu]
 let qs : Fin 8 → Program 5 := ![ty,ch,ob,typedHead,bu,ma,ap,ca]
 let xs : Fin 5 → OTerm alpha := ![head,tail,suffix,parameter,suffixValue]
 apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs xs _
 intro beta rho v Theta hrho hq
 rw [graph2Rename]
 let ys : Fin 5 → OTerm beta := ![head.relabel rho,tail.relabel rho,suffix.relabel rho,parameter.relabel rho,suffixValue.relabel rho]
 have hxs : (fun i => (xs i).relabel rho) = ys := by
   funext i
   exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))))) i
 rw [hxs] at hq
 have q0 : Nonempty (Derivation body Theta (programGraph ty (v 0) ys)) := hq 0
 have q1 : Nonempty (Derivation body Theta (programGraph ch (v 1) ys)) := hq 1
 have q2 : Nonempty (Derivation body Theta (programGraph ob (v 2) ys)) := hq 2
 have q3 : Nonempty (Derivation body Theta (programGraph typedHead (v 3) ys)) := hq 3
 have q4 : Nonempty (Derivation body Theta (programGraph bu (v 4) ys)) := hq 4
 have q5 : Nonempty (Derivation body Theta (programGraph ma (v 5) ys)) := hq 5
 have q6 : Nonempty (Derivation body Theta (programGraph ap (v 6) ys)) := hq 6
 have q7 : Nonempty (Derivation body Theta (programGraph ca (v 7) ys)) := hq 7
 have hl := unaryRecover InternalUnpair.left (.projection 0) (v 0) (head.relabel rho) ys q0 (projectionValue 0 ys)
 have hr := unaryRecover InternalUnpair.right (.projection 0) (v 1) (head.relabel rho) ys q1 (projectionValue 0 ys)
 have hp := closedApply (InternalUnpairReverseProof.actualOriginalUnpairReverseInverse body beta (head.relabel rho) (v 0) (v 1)) (andIntro hl hr)
 have hv := binaryRecover R (.projection 0) (.projection 3) (v 2) (head.relabel rho) (parameter.relabel rho) ys q2 (projectionValue 0 ys) (projectionValue 3 ys)
 have ht := binaryRecover InternalPairing.pairing ty ob (v 3) (v 0) (v 2) ys q3 q0 q2
 have hb := binaryRecover build (.projection 1) (.projection 2) (v 4) (tail.relabel rho) (suffix.relabel rho) ys q4 (projectionValue 1 ys) (projectionValue 2 ys)
 have hm := binaryRecover (mapped R) (.projection 1) (.projection 3) (v 5) (tail.relabel rho) (parameter.relabel rho) ys q5 (projectionValue 1 ys) (projectionValue 3 ys)
 have ha := binaryRecover InternalApplicationValidityStackAppend.append ma (.projection 4) (v 6) (v 5) (suffixValue.relabel rho) ys q6 q5 (projectionValue 4 ys)
 have hcan := ternaryRecover OriginalRawSyntaxTransport.consConstructor ty ch bu (v 7) (v 0) (v 1) (v 4) ys q7 q0 q1 q4
 have hi' := renameInto hi rho Theta hrho
 rw [belowRawRename] at hi'
 have hc' := renameInto hc rho Theta hrho
 rw [graph2Rename] at hc'
 have hf' := renameInto hf rho Theta hrho
 simp only [fields,conjunctionRename,graph2Rename] at hf'
 exact atValues R (raw.relabel rho) (head.relabel rho) (tail.relabel rho) (suffix.relabel rho)
   (built.relabel rho) (parameter.relabel rho) (mappedValue.relabel rho) (suffixValue.relabel rho) (total.relabel rho)
   (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) hi' hc' hf' hp hv ht hb hm ha hcan
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentPrefixBuilderQueryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentPrefixBuilderQueryProof
