module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalCompletionIntroductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalConstructorApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalIterationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalCompletionApplicationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalLambdaTraversal OriginalLambdaTraversalInternal
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalAdditionLawsProof (add)
open InternalOriginalOrderSyntaxProof (addRelabel)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalLambdaTraversalInternalCompletion OriginalLambdaTraversalInternalCompletionSyntaxProof
open OriginalLambdaTraversalInternalCompletionBindingProof OriginalLambdaTraversalInternalCompletionIntroductionProof
open OriginalLambdaTraversalInternalIterationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {positive : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem applicationRun (leaf : Program 2)
    (value d e fn arg parameter cf ca fOut aOut produced work stack start finish : OTerm alpha)
    (hf : Nonempty (Derivation positive Delta (ApplicationFields value d e fn arg)))
    (hp : Nonempty (Derivation positive Delta (graph4 application produced d e fOut aOut)))
    (hcf : Nonempty (Derivation positive Delta (Completes leaf fn parameter cf fOut)))
    (hca : Nonempty (Derivation positive Delta (Completes leaf arg parameter ca aOut)))
    (hi : Nonempty (Derivation positive Delta (graph4 visitState start value parameter work stack)))
    (ho : Nonempty (Derivation positive Delta (graph3 returnState finish produced work stack))) :
    Nonempty (Derivation positive Delta
      (graph2 (iterate leaf) finish (suc (add cf (add ca (suc z)))) start)) := by
  apply OriginalLambdaTraversalInternalConstructorApplicationProof.cases leaf start finish value produced d e fn arg
    parameter work stack fOut aOut _ hf hp hi ho
  intro beta j Theta workRet workArg resultFn s1 s2 s3 hj hs
  simp only [graph2Rename,sucRelabel,addRelabel,zRelabel]
  have hcf' := renameInto hcf j Theta hj
  have hca' := renameInto hca j Theta hj
  rw [completesRename] at hcf' hca'
  have h1 := andLeft hs
  have hfVisit := andLeft (andRight hs)
  have hfReturn := andLeft (andRight (andRight hs))
  have haVisit := andLeft (andRight (andRight (andRight hs)))
  have haReturn := andLeft (andRight (andRight (andRight (andRight hs))))
  have hlast := andRight (andRight (andRight (andRight (andRight hs))))
  have rf := completesApply leaf (fn.relabel j) (parameter.relabel j) (cf.relabel j) (fOut.relabel j)
    workArg (stack.relabel j) s1 s2 hcf' hfVisit hfReturn
  have ra := completesApply leaf (arg.relabel j) (parameter.relabel j) (ca.relabel j) (aOut.relabel j)
    workRet resultFn s2 s3 hca' haVisit haReturn
  exact iterateAfterFirst leaf (add (cf.relabel j) (add (ca.relabel j) (suc z)))
    (start.relabel j) s1 (finish.relabel j) h1
    (iterateCompose leaf (cf.relabel j) (add (ca.relabel j) (suc z)) s1 s2 (finish.relabel j) rf
      (iterateCompose leaf (ca.relabel j) (suc z) s2 s3 (finish.relabel j) ra
        (iterateOne leaf s3 (finish.relabel j) hlast)))

theorem applicationComplete (leaf : Program 2)
    (value d e fn arg parameter cf ca fOut aOut produced : OTerm alpha)
    (hf : Nonempty (Derivation positive Delta (ApplicationFields value d e fn arg)))
    (hp : Nonempty (Derivation positive Delta (graph4 application produced d e fOut aOut)))
    (hcf : Nonempty (Derivation positive Delta (Completes leaf fn parameter cf fOut)))
    (hca : Nonempty (Derivation positive Delta (Completes leaf arg parameter ca aOut))) :
    Nonempty (Derivation positive Delta
      (Completes leaf value parameter (suc (add cf (add ca (suc z)))) produced)) := by
  apply completesByRuns
  intro beta j Theta work stack start finish hj hi ho
  simp only [sucRelabel,addRelabel,zRelabel]
  have hf' := renameInto hf j Theta hj
  have hp' := renameInto hp j Theta hj
  have hcf' := renameInto hcf j Theta hj
  have hca' := renameInto hca j Theta hj
  simp only [ApplicationFields,conjunctionRename,graph1Rename,
    SourceComputabilityFormulaSupportProof.numeral,sucRelabel,zRelabel] at hf'
  rw [graph4Rename] at hp'
  rw [completesRename] at hcf' hca'
  exact applicationRun leaf (value.relabel j) (d.relabel j) (e.relabel j) (fn.relabel j) (arg.relabel j)
    (parameter.relabel j) (cf.relabel j) (ca.relabel j) (fOut.relabel j) (aOut.relabel j)
    (produced.relabel j) work stack start finish hf' hp' hcf' hca' hi ho

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalCompletionApplicationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalCompletionApplicationProof
