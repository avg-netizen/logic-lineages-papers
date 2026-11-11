module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphReconstructionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open OriginalLambdaConstructor OriginalLambdaConstructorGraphSyntaxProof OriginalLambdaConstructorGraphSupportProof
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- All intermediate pair witnesses are internal. The body selector supplies
both its original payload and its outer codomain; no new body is chosen. -/
theorem constructorReconstruction (out d e b arrowCode : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (Fields out d e b arrowCode))) :
    Nonempty (Derivation body Delta (graph3 constructor out d e b)) := by
  let node : Program 1 := rightOf (.projection 0)
  let inner : Program 1 := rightOf node
  let qs : Fin 3 → Program 1 := ![node,inner,bodyPayload]
  let xs : Fin 1 → OTerm alpha := Fin.cons out Fin.elim0
  apply queryCases qs xs _
  intro beta j ys Theta hj hq
  rw [graph3Rename]
  have hf' := renameInto hf j Theta hj
  rw [fieldsRename] at hf'
  simp only [xs,consTermRename,emptyRename] at hq
  let xx : Fin 1 → OTerm beta := Fin.cons (out.relabel j) Fin.elim0
  have hnode := unaryRecover InternalUnpair.right (.projection 0) (ys 0) (out.relabel j) xx
    (hq 0) (projectionValue 0 xx)
  have hinner := unaryRecover InternalUnpair.right node (ys 1) (ys 0) xx (hq 1) (hq 0)
  have hpayload := unaryRecover InternalUnpair.right inner (ys 2) (ys 1) xx (hq 2) (hq 1)
  have htag := unaryRecover InternalUnpair.left node (numeral 1) (ys 0) xx
    (andLeft hf') (hq 0)
  have hdomain := unaryRecover InternalUnpair.left inner (d.relabel j) (ys 1) xx
    (andLeft (andRight (andRight (andRight hf')))) (hq 1)
  have ho := reconstructPair (out.relabel j) (arrowCode.relabel j) (ys 0)
    (andLeft (andRight hf')) hnode
  have hn := reconstructPair (ys 0) (numeral 1) (ys 1) htag hinner
  have hi := reconstructPair (ys 1) (d.relabel j) (ys 2) hdomain hpayload
  have hb := bodyCodeRecover (b.relabel j) (e.relabel j) (out.relabel j) (ys 2)
    (andRight (andRight (andRight (andRight hf')))) (hq 2)
  have hpacked := packedAtPairs (out.relabel j) (d.relabel j) (e.relabel j) (ys 2)
    (arrowCode.relabel j) (ys 1) (ys 0) (andLeft (andRight (andRight hf'))) hi hn ho
  exact constructorBackward (out.relabel j) (d.relabel j) (e.relabel j) (b.relabel j) (ys 2)
    (pairRight (b.relabel j) (e.relabel j) (ys 2) hb) hpacked

theorem actualOriginalLambdaConstructorReconstruction :
    OriginalLambdaConstructorTargets.ActualOriginalLambdaConstructorReconstruction := by
  intro body alpha Delta out d e b arrowCode
  obtain ⟨h⟩ := constructorReconstruction (body := body)
    (Delta := Fields out d e b arrowCode :: Delta) out d e b arrowCode
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphReconstructionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphReconstructionProof
