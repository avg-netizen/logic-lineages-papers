module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenInverseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorErasureSyntax
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenSharedProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open EvaluatorChildrenInverseProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open SixSol20261113.Erasure.EvaluatorErasureDefinitions
open SixSol20261113.Erasure.EvaluatorErasureSyntax

theorem application (R : Program 2) (H G : Program 1) (M W : Program 2)
    (left right parameter out fn arg otherFn otherArg : OTerm alpha)
    (hsl : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) left parameter)))
    (hvl : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) out left parameter)))
    (htl : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.tag (numeral 2) left parameter)))
    (hfl : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.functionPacked fn left parameter)))
    (hal : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.argumentPacked arg left parameter)))
    (hsr : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) right parameter)))
    (hvr : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) out right parameter)))
    (htr : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.tag (numeral 2) right parameter)))
    (hfr : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.functionPacked otherFn right parameter)))
    (har : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.argumentPacked otherArg right parameter)))
    : Nonempty (Derivation body Delta (SameEvaluator R fn otherFn parameter ⊓ SameEvaluator R arg otherArg parameter)) := by
  let q0 : Program 1 := rightOf (.projection 0)
  let q1 : Program 1 := leftOf (q0)
  let q2 : Program 1 := rightOf (q1)
  let q3 : Program 1 := rightOf (q2)
  let q4 : Program 1 := rightOf (q3)
  let q5 : Program 1 := leftOf (q4)
  let q6 : Program 1 := rightOf (q4)
  let q7 : Program 1 := rightOf (q5)
  let q8 : Program 1 := rightOf (q6)
  let qs : Fin 9 → Program 1 := ![q0,q1,q2,q3,q4,q5,q6,q7,q8]
  let xs : Fin 1 → OTerm alpha := ![out]
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs xs _
  intro beta j ys Theta hj hq
  let xx : Fin 1 → OTerm beta := ![out.relabel j]
  have hx : (fun i => (xs i).relabel j) = xx := by
    funext i
    exact Fin.cases rfl (fun k => Fin.elim0 k) i
  rw [hx] at hq
  have h0 := unaryRecover InternalUnpair.right (.projection 0) (ys 0) (out.relabel j) xx (hq 0) (projectionValue 0 xx)
  have h1 := unaryRecover InternalUnpair.left (q0) (ys 1) (ys 0) xx (hq 1) (hq 0)
  have h2 := unaryRecover InternalUnpair.right (q1) (ys 2) (ys 1) xx (hq 2) (hq 1)
  have h3 := unaryRecover InternalUnpair.right (q2) (ys 3) (ys 2) xx (hq 3) (hq 2)
  have h4 := unaryRecover InternalUnpair.right (q3) (ys 4) (ys 3) xx (hq 4) (hq 3)
  have h5 := unaryRecover InternalUnpair.left (q4) (ys 5) (ys 4) xx (hq 5) (hq 4)
  have h6 := unaryRecover InternalUnpair.right (q4) (ys 6) (ys 4) xx (hq 6) (hq 4)
  have h7 := unaryRecover InternalUnpair.right (q5) (ys 7) (ys 5) xx (hq 7) (hq 5)
  have h8 := unaryRecover InternalUnpair.right (q6) (ys 8) (ys 6) xx (hq 8) (hq 6)
  have hsl' := renameInto hsl j Theta hj
  have hvl' := renameInto hvl j Theta hj
  have htl' := renameInto htl j Theta hj
  have hfl' := renameInto hfl j Theta hj
  have hal' := renameInto hal j Theta hj
  have hsr' := renameInto hsr j Theta hj
  have hvr' := renameInto hvr j Theta hj
  have htr' := renameInto htr j Theta hj
  have hfr' := renameInto hfr j Theta hj
  have har' := renameInto har j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hsl' hvl' htl' hfl' hal' hsr' hvr' htr' hfr' har'
  have rootl := recursiveRoot R H G M W (left.relabel j) (parameter.relabel j) (out.relabel j) (ys 0) (ys 1) hsl' hvl' h0 h1
  have childl := EvaluatorChildrenInverseProof.applicationAt (OriginalHereditaryEvaluatorDefinitions.evaluator R)
    (left.relabel j) (parameter.relabel j) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) (ys 6) (ys 7) (ys 8) (fn.relabel j) (arg.relabel j) htl' hfl' hal' rootl h2 h3 h4 h5 h6 h7 h8
  have rootr := recursiveRoot R H G M W (right.relabel j) (parameter.relabel j) (out.relabel j) (ys 0) (ys 1) hsr' hvr' h0 h1
  have childr := EvaluatorChildrenInverseProof.applicationAt (OriginalHereditaryEvaluatorDefinitions.evaluator R)
    (right.relabel j) (parameter.relabel j) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) (ys 6) (ys 7) (ys 8) (otherFn.relabel j) (otherArg.relabel j) htr' hfr' har' rootr h2 h3 h4 h5 h6 h7 h8
  simp only [conjunctionRename,sameRename]
  exact andIntro
    (sameIntro R (fn.relabel j) (otherFn.relabel j) (parameter.relabel j) (ys 7) (andIntro (andLeft childl) (andLeft childr)))
    (sameIntro R (arg.relabel j) (otherArg.relabel j) (parameter.relabel j) (ys 8) (andIntro (andRight childl) (andRight childr)))

theorem lambda (R : Program 2) (H G : Program 1) (M W : Program 2)
    (left right parameter out child otherChild childParameter : OTerm alpha)
    (hsl : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) left parameter)))
    (hvl : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) out left parameter)))
    (htl : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.tag (numeral 1) left parameter)))
    (hcl : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.bodyPacked child left parameter)))
    (hpl : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.childParameter childParameter left parameter)))
    (hsr : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) right parameter)))
    (hvr : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) out right parameter)))
    (htr : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.tag (numeral 1) right parameter)))
    (hcr : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.bodyPacked otherChild right parameter)))
    (hpr : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.childParameter childParameter right parameter)))
    : Nonempty (Derivation body Delta (SameEvaluator R child otherChild childParameter)) := by
  let q0 : Program 1 := rightOf (.projection 0)
  let q1 : Program 1 := leftOf (q0)
  let q2 : Program 1 := rightOf (q1)
  let q3 : Program 1 := rightOf (q2)
  let q4 : Program 1 := rightOf (q3)
  let q5 : Program 1 := rightOf (q4)
  let qs : Fin 6 → Program 1 := ![q0,q1,q2,q3,q4,q5]
  let xs : Fin 1 → OTerm alpha := ![out]
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs xs _
  intro beta j ys Theta hj hq
  let xx : Fin 1 → OTerm beta := ![out.relabel j]
  have hx : (fun i => (xs i).relabel j) = xx := by
    funext i
    exact Fin.cases rfl (fun k => Fin.elim0 k) i
  rw [hx] at hq
  have h0 := unaryRecover InternalUnpair.right (.projection 0) (ys 0) (out.relabel j) xx (hq 0) (projectionValue 0 xx)
  have h1 := unaryRecover InternalUnpair.left (q0) (ys 1) (ys 0) xx (hq 1) (hq 0)
  have h2 := unaryRecover InternalUnpair.right (q1) (ys 2) (ys 1) xx (hq 2) (hq 1)
  have h3 := unaryRecover InternalUnpair.right (q2) (ys 3) (ys 2) xx (hq 3) (hq 2)
  have h4 := unaryRecover InternalUnpair.right (q3) (ys 4) (ys 3) xx (hq 4) (hq 3)
  have h5 := unaryRecover InternalUnpair.right (q4) (ys 5) (ys 4) xx (hq 5) (hq 4)
  have hsl' := renameInto hsl j Theta hj
  have hvl' := renameInto hvl j Theta hj
  have htl' := renameInto htl j Theta hj
  have hcl' := renameInto hcl j Theta hj
  have hpl' := renameInto hpl j Theta hj
  have hsr' := renameInto hsr j Theta hj
  have hvr' := renameInto hvr j Theta hj
  have htr' := renameInto htr j Theta hj
  have hcr' := renameInto hcr j Theta hj
  have hpr' := renameInto hpr j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hsl' hvl' htl' hcl' hpl' hsr' hvr' htr' hcr' hpr'
  have rootl := recursiveRoot R H G M W (left.relabel j) (parameter.relabel j) (out.relabel j) (ys 0) (ys 1) hsl' hvl' h0 h1
  have childl := EvaluatorChildrenInverseProof.lambdaAt (OriginalHereditaryEvaluatorDefinitions.evaluator R)
    (left.relabel j) (parameter.relabel j) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) (child.relabel j) (childParameter.relabel j) htl' hcl' hpl' rootl h2 h3 h4 h5
  have rootr := recursiveRoot R H G M W (right.relabel j) (parameter.relabel j) (out.relabel j) (ys 0) (ys 1) hsr' hvr' h0 h1
  have childr := EvaluatorChildrenInverseProof.lambdaAt (OriginalHereditaryEvaluatorDefinitions.evaluator R)
    (right.relabel j) (parameter.relabel j) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) (otherChild.relabel j) (childParameter.relabel j) htr' hcr' hpr' rootr h2 h3 h4 h5
  simp only [conjunctionRename,sameRename]
  exact sameIntro R (child.relabel j) (otherChild.relabel j) (childParameter.relabel j) (ys 5) (andIntro childl childr)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenSharedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenSharedProof
