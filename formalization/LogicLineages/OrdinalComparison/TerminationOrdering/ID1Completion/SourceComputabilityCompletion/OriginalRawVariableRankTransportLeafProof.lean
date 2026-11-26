module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankTransportVariableProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankTransportLeafProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof (refl symm trans congSuc)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternal OriginalRawVariableRank
open OriginalRawVariableRankTransport
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
open OriginalRawVariableRankTransportArithmeticProof OriginalRawVariableRankTransportSyntaxProof
open OriginalRawVariableRankTransportVariableProof
open InternalOriginalPairingOrderArithmeticProof (formulaCases withHyp)
open OriginalRawSyntaxTransportInternalFoldLeafConstructorsProof
open OriginalRawSyntaxTransportInternalCancellationLeafProof

theorem nonzeroLeafTransport (erasing : Bool) (raw transformed before after d k tag : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 rawTag tag raw)))
    (hn : Nonempty (Derivation body Delta (equal tag z).not))
    (harity : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) z raw)))
    (htransform : Nonempty (Derivation body Delta (graph3 (fold (transformMode erasing)) transformed d k raw)))
    (hb : Nonempty (Derivation body Delta (graph1 variableRankRaw before raw)))
    (ha : Nonempty (Derivation body Delta (graph1 variableRankRaw after transformed))) :
    Nonempty (Derivation body Delta (RankRelation erasing after before)) := by
  have he : Nonempty (Derivation body Delta (equal transformed raw)) := by
    cases erasing <;> exact unchangedForward _ raw transformed d k tag harity ht hn htransform
  have he' : Nonempty (Derivation body Delta (eqn transformed raw)) := by simpa only [equalEqn] using he
  have ha' := headTransport variableRankRaw after transformed raw Fin.elim0 he' ha
  apply relationOfEqual erasing after before
  simpa only [equalEqn] using valueUnique variableRankRaw after before (Fin.cons raw Fin.elim0) ha' hb

/-- Total raw leaf coverage includes every malformed tag-six payload and every
unknown nonstructural tag, not just decoded original syntax. -/
theorem leafTransport (erasing : Bool) (raw transformed before after d k : OTerm alpha)
    (harity : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) z raw)))
    (ht : Nonempty (Derivation body Delta (graph3 (fold (transformMode erasing)) transformed d k raw)))
    (hb : Nonempty (Derivation body Delta (graph1 variableRankRaw before raw)))
    (ha : Nonempty (Derivation body Delta (graph1 variableRankRaw after transformed))) :
    Nonempty (Derivation body Delta (RankRelation erasing after before)) := by
  apply programCases rawTag (Fin.cons raw Fin.elim0) _
  intro beta j Theta tag hj htag
  rw [rankRelationRename]
  simp only [consTermRename,emptyRename] at htag
  have harity' := renameInto harity j Theta hj
  have ht' := renameInto ht j Theta hj
  have hb' := renameInto hb j Theta hj
  have ha' := renameInto ha j Theta hj
  simp only [graph1Rename,zRelabel] at harity'
  rw [graph3Rename] at ht'
  rw [graph1Rename] at hb' ha'
  apply formulaCases (equal tag z)
  · have he : Nonempty (Derivation body (equal tag z :: Theta) (equal tag z)) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have he' : Nonempty (Derivation body (equal tag z :: Theta) (eqn tag z)) := by
      simpa only [equalEqn] using he
    have hzero := outputTransport rawTag tag z (Fin.cons (raw.relabel j) Fin.elim0) he' (withHyp htag _)
    apply variableCases (raw.relabel j) _ hzero
    intro gamma l Xi index hl hvariable
    rw [rankRelationRename]
    have ht'' := renameInto (withHyp ht' (equal tag z)) l Xi hl
    have hb'' := renameInto (withHyp hb' (equal tag z)) l Xi hl
    have ha'' := renameInto (withHyp ha' (equal tag z)) l Xi hl
    rw [graph3Rename] at ht''
    rw [graph1Rename] at hb'' ha''
    exact variableTransport erasing ((raw.relabel j).relabel l) ((transformed.relabel j).relabel l)
      ((before.relabel j).relabel l) ((after.relabel j).relabel l)
      ((d.relabel j).relabel l) ((k.relabel j).relabel l) index hvariable ht'' hb'' ha''
  · exact nonzeroLeafTransport erasing (raw.relabel j) (transformed.relabel j)
      (before.relabel j) (after.relabel j) (d.relabel j) (k.relabel j) tag
      (withHyp htag _) ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp harity' _)
      (withHyp ht' _) (withHyp hb' _) (withHyp ha' _)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankTransportLeafProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankTransportLeafProof
