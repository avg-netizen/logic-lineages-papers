module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLambdaSelectorProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalBodySelectorProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (eqn eqnRelabel)
open OriginalLambdaTraversalLambdaSelectorProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Rebuilding the SAME original lambda forces the SAME typed body. The
constructor drops only the outer child type, and its supplied actual type
restores that coordinate; selector functionality then gives full equality. -/
theorem fromRebuild (raw d e child childOut : OTerm alpha)
    (he : Nonempty (Derivation body Delta (graph1 OriginalLambdaTraversal.rawCodomain e raw)))
    (hb : Nonempty (Derivation body Delta (graph1 OriginalLambdaTraversal.rawBody child raw)))
    (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left e childOut)))
    (hc : Nonempty (Derivation body Delta (graph3 OriginalLambdaConstructor.constructor raw d e childOut))) :
    Nonempty (Derivation body Delta (eqn childOut child)) := by
  apply programCases OriginalLambdaConstructor.arrow (Fin.cons d (Fin.cons e Fin.elim0)) _
  intro beta j Theta arrow hj ha
  rw [eqnRelabel]
  have he' := renameInto he j Theta hj
  have hb' := renameInto hb j Theta hj
  have ht' := renameInto ht j Theta hj
  have hc' := renameInto hc j Theta hj
  rw [graph1Rename] at he' hb' ht'
  rw [graph3Rename] at hc'
  simp only [consTermRename,emptyRename] at ha
  have fields := OriginalLambdaConstructorGraphFieldsProof.constructorFields
    (raw.relabel j) (d.relabel j) (e.relabel j) (childOut.relabel j) arrow hc' ht' ha
  have outputBody := andRight (andRight (andRight (andRight fields)))
  have inputBody := bodyCodeAt (raw.relabel j) (e.relabel j) (child.relabel j) he' hb'
  exact valueUnique OriginalLambdaConstructor.bodyCode (childOut.relabel j) (child.relabel j)
    (Fin.cons (e.relabel j) (Fin.cons (raw.relabel j) Fin.elim0)) outputBody inputBody

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalBodySelectorProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalBodySelectorProof
