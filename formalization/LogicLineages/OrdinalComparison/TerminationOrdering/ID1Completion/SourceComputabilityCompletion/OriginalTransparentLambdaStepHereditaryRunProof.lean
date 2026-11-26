module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepHereditaryControlProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRepeatProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepHereditaryRunProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph InternalGraphComposition
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalRecursionGraphStepSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open OriginalHereditaryLambda
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Lift the child's actual successful hereditary run along one paid
original transition. The finish state is identical, not newly guessed. -/
theorem guardBackward (oldStep : Program 4)
    (xs ys : Fin 4 → OTerm alpha) (code tail state next : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph path code xs)))
    (ht : Nonempty (Derivation body Delta (programGraph path tail ys)))
    (hl : Nonempty (Derivation body Delta (programGraph live state xs)))
    (hn : Nonempty (Derivation body Delta (programGraph live next ys)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code z tail)))
    (hstep : Nonempty (Derivation body Delta (graph1 (transition oldStep) next state)))
    (hout : Nonempty (Derivation body Delta (programGraph (guard oldStep) (suc z) ys))) :
    Nonempty (Derivation body Delta (programGraph (guard oldStep) (suc z) xs)) := by
  apply programCases (run oldStep) ys _
  intro beta j Gamma result hj hr
  simp only [programRename,sucRelabel,zRelabel]
  have hp' := renameInto hp j Gamma hj
  have ht' := renameInto ht j Gamma hj
  have hl' := renameInto hl j Gamma hj
  have hn' := renameInto hn j Gamma hj
  have hc' := renameInto hc j Gamma hj
  have hstep' := renameInto hstep j Gamma hj
  have hout' := renameInto hout j Gamma hj
  simp only [programRename,sucRelabel,zRelabel] at hp' ht' hl' hn' hout'
  simp only [graph2Rename,zRelabel] at hc'
  simp only [graph1Rename] at hstep'
  let xx := fun i => (xs i).relabel j
  let yy := fun i => (ys i).relabel j
  have hfinish := unaryRecover finish (run oldStep) (suc z) result yy hout' hr
  have hrepeat := binaryRecover (InternalRawListRepeat.repeatProgram (transition oldStep))
    path live result (tail.relabel j) (next.relabel j) yy hr ht' hn'
  have hparent := InternalRawListRepeatProof.frontConsBackward (transition oldStep)
    (code.relabel j) z (tail.relabel j) result (state.relabel j) (next.relabel j) hc' hstep' hrepeat
  have hrun := binaryValue (InternalRawListRepeat.repeatProgram (transition oldStep)) path live
    result (code.relabel j) (state.relabel j) xx hparent hp' hl'
  exact unaryValue finish (run oldStep) (suc z) result xx hfinish hrun
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepHereditaryRunProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepHereditaryRunProof
