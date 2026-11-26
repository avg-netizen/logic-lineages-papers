module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldLambdaProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldOrdinaryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankUnaryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalTagArithmeticSupportProof (refl symm)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternal OriginalRawVariableRank
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
open OriginalRawVariableRankSupportProof
open OriginalRawSyntaxTransportInternalParametersQueryProof
open OriginalRawSyntaxTransportInternalFoldLambdaProof OriginalRawSyntaxTransportInternalFoldOrdinaryProof

theorem rankLambdaForward (raw out domain child : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 lambdaConstructor raw domain child)))
    (ho : Nonempty (Derivation body Delta (graph1 variableRankRaw out raw))) :
    Nonempty (Derivation body Delta (graph1 variableRankRaw out child)) := by
  apply ternaryCases (fold .rank) z (suc z) child _
  intro beta j Theta childRank hj hchild
  rw [graph1Rename]
  have hc' := renameInto hc j Theta hj
  have ho' := renameInto ho j Theta hj
  rw [graph2Rename] at hc'
  rw [graph1Rename] at ho'
  simp only [zRelabel,sucRelabel] at hchild
  have he := lambdaForward .rank (raw.relabel j) (out.relabel j) z (z)
    (domain.relabel j) (child.relabel j) childRank hc' hchild
    (rankToFold (out.relabel j) z z (raw.relabel j) ho')
  simp only [UnaryResult,equalEqn] at he
  obtain ⟨he⟩ := he
  exact outputTransport variableRankRaw childRank (out.relabel j)
    (Fin.cons (child.relabel j) Fin.elim0) ⟨InternalTagArithmeticSupportProof.symm he⟩
    (rankFromFold childRank z (suc z) (child.relabel j) hchild)

theorem rankLambdaBackward (raw out domain child : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 lambdaConstructor raw domain child)))
    (ho : Nonempty (Derivation body Delta (graph1 variableRankRaw out child))) :
    Nonempty (Derivation body Delta (graph1 variableRankRaw out raw)) :=
  rankFromFold out z z raw
    (lambdaBackward .rank raw out z z domain child out hc
      (rankToFold out z (suc z) child ho) (by simpa only [UnaryResult,equalEqn] using
        (show Nonempty (Derivation body Delta (InternalTagArithmeticSyntaxProof.eqn out out)) from
          ⟨InternalTagArithmeticSupportProof.refl out⟩)))

theorem rankOrdinaryForward (raw out head child : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 ordinaryConstructor raw head child)))
    (ho : Nonempty (Derivation body Delta (graph1 variableRankRaw out raw))) :
    Nonempty (Derivation body Delta (graph1 variableRankRaw out child)) := by
  apply ternaryCases (fold .rank) z (z) child _
  intro beta j Theta childRank hj hchild
  rw [graph1Rename]
  have hc' := renameInto hc j Theta hj
  have ho' := renameInto ho j Theta hj
  rw [graph2Rename] at hc'
  rw [graph1Rename] at ho'
  simp only [zRelabel,sucRelabel] at hchild
  have he := ordinaryForward .rank (raw.relabel j) (out.relabel j) z (z)
    (head.relabel j) (child.relabel j) childRank hc' hchild
    (rankToFold (out.relabel j) z z (raw.relabel j) ho')
  simp only [UnaryResult,equalEqn] at he
  obtain ⟨he⟩ := he
  exact outputTransport variableRankRaw childRank (out.relabel j)
    (Fin.cons (child.relabel j) Fin.elim0) ⟨InternalTagArithmeticSupportProof.symm he⟩
    (rankFromFold childRank z (z) (child.relabel j) hchild)

theorem rankOrdinaryBackward (raw out head child : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 ordinaryConstructor raw head child)))
    (ho : Nonempty (Derivation body Delta (graph1 variableRankRaw out child))) :
    Nonempty (Derivation body Delta (graph1 variableRankRaw out raw)) :=
  rankFromFold out z z raw
    (ordinaryBackward .rank raw out z z head child out hc
      (rankToFold out z (z) child ho) (by simpa only [UnaryResult,equalEqn] using
        (show Nonempty (Derivation body Delta (InternalTagArithmeticSyntaxProof.eqn out out)) from
          ⟨InternalTagArithmeticSupportProof.refl out⟩)))


end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankUnaryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankUnaryProof
