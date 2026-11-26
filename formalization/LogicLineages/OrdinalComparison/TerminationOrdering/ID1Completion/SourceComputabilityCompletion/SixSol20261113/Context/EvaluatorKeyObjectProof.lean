module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyObjectSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyObjectProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof
open UniformCertificateCompletion EvaluatorKeyPut
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
attribute [local irreducible] programGraph
theorem actualObjectEquality : EvaluatorKeyObjectTargets.ActualObjectEquality := by
 intro p H G W P body alpha Delta leftObject rightObject leftRaw rightRaw leftOut rightOut context gamma parameter
   pl pr pp dl dr same kl kr
 let F := EvaluatorKeyFinalFoldDefinitions.fold p H G W P
 let qs : Fin 2 → Program 3 := ![.composition F ![.projection 0,.projection 2],.composition F ![.projection 1,.projection 2] ]
 let xs : Fin 3 → OTerm alpha := ![leftRaw,rightRaw,parameter]
 apply OriginalRawSyntaxTransportInternalParserSupportProof.programsCases qs xs _
 intro beta j Theta values hj hg
 have hx : (fun i => (xs i).relabel j) = (![leftRaw.relabel j,rightRaw.relabel j,parameter.relabel j] : Fin 3 → OTerm beta) := by
   funext i
   exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))) i
 rw [hx] at hg
 let xx : Fin 3 → OTerm beta := ![leftRaw.relabel j,rightRaw.relabel j,parameter.relabel j]
 have fl := binaryRecover F (.projection 0) (.projection 2) (values 0) (leftRaw.relabel j) (parameter.relabel j) xx (hg 0) (projectionValue 0 xx) (projectionValue 2 xx)
 have fr := binaryRecover F (.projection 1) (.projection 2) (values 1) (rightRaw.relabel j) (parameter.relabel j) xx (hg 1) (projectionValue 1 xx) (projectionValue 2 xx)
 have pl' := renameInto pl j Theta hj
 have pr' := renameInto pr j Theta hj
 have pp' := renameInto pp j Theta hj
 have dl' := renameInto dl j Theta hj
 have dr' := renameInto dr j Theta hj
 have same' := renameInto same j Theta hj
 have kl' := renameInto kl j Theta hj
 have kr' := renameInto kr j Theta hj
 rw [graph2Rename] at pl' pr' pp' kl' kr'
 simp only [Domain,OriginalActiveKernelMinimumSupportProof.domainRename] at dl' dr'
 simp only [Same,SixSol20261113.Erasure.EvaluatorErasureSyntax.sameRename] at same'
 rw [equalEqn,InternalTagArithmeticSyntaxProof.eqnRelabel,← equalEqn]
 have he := EvaluatorKeyFinalFoldProof.actualFinalFoldEquality p H G W P body beta Theta
   (leftRaw.relabel j) (rightRaw.relabel j) (values 0) (values 1) (parameter.relabel j) dl' dr' same' fl fr
 have pol := EvaluatorKeyObjectSupportProof.outputPair (refined p H G W P)
   (context.relabel j) (leftObject.relabel j) (leftOut.relabel j) (gamma.relabel j) (leftRaw.relabel j)
   (parameter.relabel j) (values 0) pl' pp' fl kl'
 have por := EvaluatorKeyObjectSupportProof.outputPair (refined p H G W P)
   (context.relabel j) (rightObject.relabel j) (rightOut.relabel j) (gamma.relabel j) (rightRaw.relabel j)
   (parameter.relabel j) (values 1) pr' pp' fr kr'
 exact EvaluatorKeyObjectSupportProof.equalPairs (leftOut.relabel j) (rightOut.relabel j) (gamma.relabel j)
   (values 0) (values 1) he pol por
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyObjectProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyObjectProof
