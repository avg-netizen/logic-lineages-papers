module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EntryFinalQueriesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesNonConsCoherence.StepProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EntryNonConsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261115.OriginalBoundsRecombination (maximum merge)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalTagArithmeticSyntaxProof (z suc eqn)
open OriginalTypedDecoderTransportLogicalProof (notRename)
open SourceComputabilityFormulaSupportProof (numeral)
open Continuation20261114
open ArgumentEntriesNonConsCoherence.StepProof (caseFormula caseRename canonicalLayer)

theorem nonCons (six : Bool) (raw tag param : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left tag raw)))
    (hn : Nonempty (Derivation body Delta (eqn tag (numeral 7)).not))
    (hc : Nonempty (Derivation body Delta (caseFormula six tag))) :
    Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (numeral (if six then 1 else 0)) raw param)) := by
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases EntryFinalQueriesProof.queries ![raw,param] _
  intro beta j ys Theta hj hq
  have hx : (fun i => (![raw,param] i).relabel j) = ![raw.relabel j,param.relabel j] := by
    funext i; fin_cases i <;> rfl
  rw [hx] at hq
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  have htj := renameInto ht j Theta hj
  have hnj := renameInto hn j Theta hj
  have hcj := renameInto hc j Theta hj
  rw [graph1Rename] at htj
  simp only [notRename,InternalTagArithmeticSyntaxProof.eqnRelabel,GuardedSourceSyntaxProof.numeralRename] at hnj
  rw [caseRename] at hcj
  obtain ⟨hold,hdeps,hanswers⟩ := EntryFinalQueriesProof.recover (raw.relabel j) (param.relabel j) ys hq
  exact ArgumentEntriesConsTable.FinalProof.finalAnswers body beta Theta ArgumentEntriesRecursor.rank
    ArgumentEntriesRecursor.dependency ArgumentEntriesRecursor.layer (raw.relabel j) (param.relabel j)
    (raw.relabel j) (ys 0) (ys 1) (ys 2) (numeral (if six then 1 else 0))
    (projectionValue 0 ![raw.relabel j,param.relabel j]) hold hdeps hanswers
    (canonicalLayer six (raw.relabel j) (tag.relabel j) (ys 2) (param.relabel j) htj hnj hcj)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EntryNonConsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EntryNonConsProof
