module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenSharedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenAssemblyProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open EvaluatorChildrenSharedProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open SixSol20261113.Erasure.EvaluatorErasureDefinitions
open SixSol20261113.Erasure.EvaluatorErasureSyntax

theorem application (R : Program 2) (H G : Program 1) (M W : Program 2)
    (left right parameter fn arg otherFn otherArg : OTerm alpha)
    (had : Nonempty (Derivation body Delta (AdmittedPair R H G M W left right parameter)))
    (hs0 : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) fn parameter)))
    (hs1 : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) arg parameter)))
    (hs2 : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) otherFn parameter)))
    (hs3 : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) otherArg parameter)))
    (htl : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.tag (numeral 2) left parameter)))
    (hfl : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.functionPacked fn left parameter)))
    (hal : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.argumentPacked arg left parameter)))
    (htr : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.tag (numeral 2) right parameter)))
    (hfr : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.functionPacked otherFn right parameter)))
    (har : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.argumentPacked otherArg right parameter)))
    : Nonempty (Derivation body Delta (AdmittedPair R H G M W fn otherFn parameter ⊓ AdmittedPair R H G M W arg otherArg parameter)) := by
  have hsl := andLeft had
  have hsr := andLeft (andRight had)
  have he := andRight (andRight had)
  apply sameCases R left right parameter _ he
  intro beta j Theta out hj hv
  have hsl' := renameInto hsl j Theta hj
  have hsr' := renameInto hsr j Theta hj
  have hs0' := renameInto hs0 j Theta hj
  have hs1' := renameInto hs1 j Theta hj
  have hs2' := renameInto hs2 j Theta hj
  have hs3' := renameInto hs3 j Theta hj
  have htl' := renameInto htl j Theta hj
  have hfl' := renameInto hfl j Theta hj
  have hal' := renameInto hal j Theta hj
  have htr' := renameInto htr j Theta hj
  have hfr' := renameInto hfr j Theta hj
  have har' := renameInto har j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hsl' hsr' hs0' hs1' hs2' hs3' htl' hfl' hal' htr' hfr' har'
  have hc := EvaluatorChildrenSharedProof.application R H G M W
    (left.relabel j) (right.relabel j) (parameter.relabel j) out (fn.relabel j) (arg.relabel j) (otherFn.relabel j) (otherArg.relabel j)
    hsl' (andLeft hv) htl' hfl' hal' hsr' (andRight hv) htr' hfr' har'
  simp only [conjunctionRename,admittedRename]
  exact andIntro (andIntro hs0' (andIntro hs2' (andLeft hc)))
    (andIntro hs1' (andIntro hs3' (andRight hc)))

theorem lambda (R : Program 2) (H G : Program 1) (M W : Program 2)
    (left right parameter child otherChild childParameter : OTerm alpha)
    (had : Nonempty (Derivation body Delta (AdmittedPair R H G M W left right parameter)))
    (hs0 : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) child childParameter)))
    (hs1 : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) otherChild childParameter)))
    (htl : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.tag (numeral 1) left parameter)))
    (hcl : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.bodyPacked child left parameter)))
    (hpl : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.childParameter childParameter left parameter)))
    (htr : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.tag (numeral 1) right parameter)))
    (hcr : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.bodyPacked otherChild right parameter)))
    (hpr : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.childParameter childParameter right parameter)))
    : Nonempty (Derivation body Delta (AdmittedPair R H G M W child otherChild childParameter)) := by
  have hsl := andLeft had
  have hsr := andLeft (andRight had)
  have he := andRight (andRight had)
  apply sameCases R left right parameter _ he
  intro beta j Theta out hj hv
  have hsl' := renameInto hsl j Theta hj
  have hsr' := renameInto hsr j Theta hj
  have hs0' := renameInto hs0 j Theta hj
  have hs1' := renameInto hs1 j Theta hj
  have htl' := renameInto htl j Theta hj
  have hcl' := renameInto hcl j Theta hj
  have hpl' := renameInto hpl j Theta hj
  have htr' := renameInto htr j Theta hj
  have hcr' := renameInto hcr j Theta hj
  have hpr' := renameInto hpr j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hsl' hsr' hs0' hs1' htl' hcl' hpl' htr' hcr' hpr'
  have hc := EvaluatorChildrenSharedProof.lambda R H G M W
    (left.relabel j) (right.relabel j) (parameter.relabel j) out (child.relabel j) (otherChild.relabel j) (childParameter.relabel j)
    hsl' (andLeft hv) htl' hcl' hpl' hsr' (andRight hv) htr' hcr' hpr'
  simp only [conjunctionRename,admittedRename]
  exact andIntro hs0' (andIntro hs1' hc)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenAssemblyProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenAssemblyProof
