module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalBodySelectorProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalOutputProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalBodyCanonicalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open OriginalLambdaTraversalSelection OriginalLambdaTraversalInternal
open OriginalLambdaTraversalInternalFieldsSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Parent C-fixedness determines the actual computed child output. Child
source/type/window are derived; the exact OutputLaws theorem supplies the
output's actual codomain before original selector injectivity is used. -/
theorem atOutput (rawData : Data) (window : Program 1)
    (input d e child childOut parameter bodyParameter : OTerm alpha)
    (hw : Nonempty (Derivation body Delta (OriginalFunctionNeutrality.windowGraph window input parameter)))
    (hf : Nonempty (Derivation body Delta (LambdaFields input d e child parameter bodyParameter)))
    (hs : Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity (leafData rawData window))
        InternalOriginalStepGuard.one input parameter)))
    (hp : Nonempty (Derivation body Delta (graph2 (canonical rawData window) input input parameter)))
    (hc : Nonempty (Derivation body Delta (graph2 (canonical rawData window) childOut child bodyParameter))) :
    Nonempty (Derivation body Delta (graph2 (canonical rawData window) child child bodyParameter)) := by
  have sourceChild := OriginalLambdaTraversalLambdaSourceProof.sourceChild
    rawData window input d e child parameter bodyParameter hf hs
  have windowChild := OriginalLambdaTraversalLambdaWindowProof.windowChild window
    (suc z) input child parameter bodyParameter (andRight (andRight (andRight (andRight hf)))) hw
  have output := OriginalLambdaTraversalOutputProof.invariantAtInput rawData window
    childOut child e bodyParameter (andIntro windowChild (andIntro sourceChild hc))
  have raw := OriginalLambdaTraversalInternalLambdaProof.lambdaForward (leaf rawData window)
    input d e child parameter bodyParameter childOut input hf hc hp
  have same := OriginalLambdaTraversalBodySelectorProof.fromRebuild input d e child childOut
    (andLeft (andRight (andRight hf))) (andLeft (andRight (andRight (andRight hf))))
    (andLeft (andRight output)) raw
  exact outputTransport (canonical rawData window) childOut child
    (Fin.cons child (Fin.cons bodyParameter Fin.elim0)) same hc

/-- The actual child C output is selected internally. No body-C graph,
fixedness, accessibility, or native calibration is an assumption. -/
theorem bodyFixed (rawData : Data) (window : Program 1)
    (input d e child parameter bodyParameter : OTerm alpha)
    (hw : Nonempty (Derivation body Delta (OriginalFunctionNeutrality.windowGraph window input parameter)))
    (hf : Nonempty (Derivation body Delta (LambdaFields input d e child parameter bodyParameter)))
    (hs : Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity (leafData rawData window))
        InternalOriginalStepGuard.one input parameter)))
    (hp : Nonempty (Derivation body Delta (graph2 (canonical rawData window) input input parameter))) :
    Nonempty (Derivation body Delta (graph2 (canonical rawData window) child child bodyParameter)) := by
  apply programCases (canonical rawData window) (Fin.cons child (Fin.cons bodyParameter Fin.elim0)) _
  intro beta j Theta childOut hj hc
  rw [graph2Rename]
  simp only [consTermRename,emptyRename] at hc
  have hw' := renameInto hw j Theta hj
  have hf' := renameInto hf j Theta hj
  have hs' := renameInto hs j Theta hj
  have hp' := renameInto hp j Theta hj
  simp only [OriginalFunctionNeutrality.windowGraph,OriginalVariableRepresentative.windowGraph,
    graph2Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel] at hw'
  rw [lambdaFieldsRename] at hf'
  simp only [graph2Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel] at hs'
  rw [graph2Rename] at hp'
  exact atOutput rawData window (input.relabel j) (d.relabel j) (e.relabel j) (child.relabel j)
    childOut (parameter.relabel j) (bodyParameter.relabel j) hw' hf' hs' hp' hc

/-- The full internally derived child package at the SAME C and exact
extended-Gamma parameter. Final transition transport is a separate theorem. -/
theorem bodyCanonical (rawData : Data) (window : Program 1)
    (input d e child parameter bodyParameter : OTerm alpha)
    (hw : Nonempty (Derivation body Delta (OriginalFunctionNeutrality.windowGraph window input parameter)))
    (hf : Nonempty (Derivation body Delta (LambdaFields input d e child parameter bodyParameter)))
    (hs : Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity (leafData rawData window))
        InternalOriginalStepGuard.one input parameter)))
    (hp : Nonempty (Derivation body Delta (graph2 (canonical rawData window) input input parameter))) :
    Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity (leafData rawData window))
        InternalOriginalStepGuard.one child bodyParameter ⊓
        (graph1 InternalUnpair.left e child ⊓ graph2 (canonical rawData window) child child bodyParameter))) := by
  have hsChild := OriginalLambdaTraversalLambdaSourceProof.sourceChild rawData window
    input d e child parameter bodyParameter hf hs
  exact andIntro (andLeft hsChild) (andIntro (andRight hsChild)
    (bodyFixed rawData window input d e child parameter bodyParameter hw hf hs hp))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalBodyCanonicalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalBodyCanonicalProof
