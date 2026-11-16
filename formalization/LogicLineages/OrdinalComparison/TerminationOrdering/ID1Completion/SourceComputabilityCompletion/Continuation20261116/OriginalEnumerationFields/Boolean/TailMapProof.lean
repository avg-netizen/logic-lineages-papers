module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.AnswerCasesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.TailMapProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalRecursionGraphStepSyntaxProof (consTermRename)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem recover (n : Nat) (deps child tail param values rest : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode deps child tail)))
    (hm : Nonempty (Derivation body Delta (graph2 (Equation.answerMap n) values deps param)))
    (ht : Nonempty (Derivation body Delta (graph1 InternalListCodec.tailCode rest values))) :
    Nonempty (Derivation body Delta (graph2 (Equation.answerMap n) rest tail param)) := by
  apply AnswerCasesProof.consCases n deps child tail param values _ hc hm
  intro beta j Theta old hj hr hs
  rw [graph2Rename]
  have htj := renameInto ht j Theta hj
  rw [graph1Rename] at htj
  apply programCases (extract n) (Fin.cons (child.relabel j) (Fin.cons (param.relabel j) Fin.elim0)) _
  intro gamma k Xi value hk hv
  rw [graph2Rename]
  simp only [consTermRename,emptyRename] at hv
  have htk := renameInto htj k Xi hk
  have hrk := renameInto hr k Xi hk
  have hsk := renameInto hs k Xi hk
  rw [graph1Rename] at htk
  rw [graph2Rename] at hrk
  rw [graph3Rename] at hsk
  have hcons := AnswerCasesProof.stepCons n ((child.relabel j).relabel k) (old.relabel k)
    ((param.relabel j).relabel k) ((values.relabel j).relabel k) value hsk hv
  have htail := InternalRawListRecursionSupportProof.consTail ((values.relabel j).relabel k) value (old.relabel k) hcons
  have he := valueUnique InternalListCodec.tailCode (old.relabel k) ((rest.relabel j).relabel k)
    (Fin.cons ((values.relabel j).relabel k) Fin.elim0) htail htk
  exact outputTransport (Equation.answerMap n) (old.relabel k) ((rest.relabel j).relabel k)
    ![((tail.relabel j).relabel k),((param.relabel j).relabel k)] he hrk
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.TailMapProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.TailMapProof
