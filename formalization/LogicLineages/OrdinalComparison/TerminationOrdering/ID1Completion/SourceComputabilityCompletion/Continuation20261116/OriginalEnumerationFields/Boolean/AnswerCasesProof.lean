module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.AnswersProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.MemberProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.AnswerCasesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalTagArithmeticSyntaxProof (z)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem consCases (n : Nat) (deps child tail param values : OTerm alpha) (psi : Formula alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode deps child tail)))
    (hm : Nonempty (Derivation body Delta (graph2 (Equation.answerMap n) values deps param)))
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (rest : OTerm beta),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph2 (Equation.answerMap n) rest (tail.relabel j) (param.relabel j))) →
      Nonempty (Derivation body Theta (graph3 (Equation.answerStep n) (values.relabel j) (child.relabel j) rest (param.relabel j))) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  have hs := InternalRawListRecursionProof.consForward (InternalAcceptance.constantZero 1) (Equation.answerStep n)
    deps child tail values (Fin.cons param Fin.elim0) hc hm
  apply InternalRawListRecursionProof.stepCases (InternalAcceptance.constantZero 1) (Equation.answerStep n)
    values child tail (Fin.cons param Fin.elim0) psi hs
  intro beta j Theta rest hj hr hstep
  simp only [consTermRename,emptyRename] at hr hstep
  exact next beta j Theta rest hj hr hstep

theorem stepCons (n : Nat) (child rest param values value : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph3 (Equation.answerStep n) values child rest param)))
    (hv : Nonempty (Derivation body Delta (graph2 (extract n) value child param))) :
    Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode values value rest)) := by
  have hv' := binaryValue (extract n) (.projection 0) (.projection 2) value child param ![child,rest,param]
    hv (projectionValue 0 ![child,rest,param]) (projectionValue 2 ![child,rest,param])
  exact binaryRecover InternalListCodec.consCode (.composition (extract n) ![.projection 0,.projection 2]) (.projection 1)
    values value rest ![child,rest,param] hs hv' (projectionValue 1 ![child,rest,param])
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.AnswerCasesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.AnswerCasesProof
