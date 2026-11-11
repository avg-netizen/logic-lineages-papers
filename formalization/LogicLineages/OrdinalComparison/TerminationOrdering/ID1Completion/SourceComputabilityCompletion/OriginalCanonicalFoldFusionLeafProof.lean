module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalFoldFusionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationCertifiedResultFoldClosureLeafProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalFoldFusionLeafProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open OriginalCanonicalFoldFusion OriginalCanonicalFoldFusionSyntaxProof
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- Closed-branch equality is supplied only for the actual existing leaf.
The same actual input validity, type and window accompany its graph. -/
def LeafLaw (data : Data) (window : Program 1) (leaf target : Program 2) : Prop :=
  ∀ (positive : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (out input typ parameter : OrdinaryArithmetic.Term alpha),
    Nonempty (Derivation positive Delta (premises data window leaf target out input typ parameter)) →
    Nonempty (Derivation positive Delta (graph2 target out input parameter))

/-- The actual guarded stack's closed branch returns its actual leaf.
Both the leaf witness and its equality with the supplied fold output are
proved inside the calculus. No successful child/run premise is assumed. -/
theorem closedLaw (data : Data) (window : Program 1) (leaf target : Program 2)
    (combine : Program 5) (law : LeafLaw data window leaf target) :
    ClosedLaw data window
      (InternalParameterizedApplicationResultStack.foldP
        (InternalParameterizedCanonicalResultFold.rootGuard data) leaf combine) target := by
  intro body α Gamma out input typ parameter hp hg
  apply programCases leaf (Fin.cons input (Fin.cons parameter Fin.elim0)) _
  intro β j Delta produced hj hl
  rw [outputInvariantRename]
  simp only [consTermRename,emptyRename] at hl
  have hp' := renameInto hp j Delta hj
  rw [premisesRename] at hp'
  have hg' := renameInto hg j Delta hj
  simp only [graph2Rename,zRelabel] at hg'
  have hc := InternalParameterizedApplicationCertifiedResultFoldClosureLeafProof.leafClosure
    (InternalParameterizedCanonicalResultFold.rootGuard data) leaf combine
    (input.relabel j) produced (parameter.relabel j) hg' hl
  have he := valueUnique
    (InternalParameterizedApplicationResultStack.foldP
      (InternalParameterizedCanonicalResultFold.rootGuard data) leaf combine)
    produced (out.relabel j)
    (Fin.cons (input.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0))
    (andRight hc) (andRight (andRight hp'))
  have hl' := outputTransport leaf produced (out.relabel j)
    (Fin.cons (input.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)) he hl
  exact law body β Delta (out.relabel j) (input.relabel j) (typ.relabel j) (parameter.relabel j)
    (andIntro (andLeft hp') (andIntro (andLeft (andRight hp')) hl'))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalFoldFusionLeafProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalFoldFusionLeafProof
