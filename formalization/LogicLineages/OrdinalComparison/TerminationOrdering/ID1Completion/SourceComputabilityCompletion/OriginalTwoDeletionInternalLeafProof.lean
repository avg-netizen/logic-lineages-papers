module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalVariableProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellationLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalLeafProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof
open InternalTagArithmeticSyntaxProof (eqn suc sucRelabel)
open InternalTagArithmeticSupportProof
open InternalOriginalOrderSyntaxProof (ltF orderRename)
open InternalSquareRootArithmeticSupportProof
open InternalOriginalPairingOrderArithmeticProof (withHyp weakStrictTrans)
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternal
open OriginalTwoDeletionInternalVariableArithmeticProof OriginalTwoDeletionInternalVariableRegionsProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
open OriginalRawSyntaxTransportInternalCancellationLeafProof
open OriginalRawSyntaxTransportInternalCancellationLeafSupportProof
open OriginalRawSyntaxTransportInternalConstructorLeafProof OriginalRawSyntaxTransportInternalFoldLeafProof
open InternalOriginalPairingOrderArithmeticProof (formulaCases)
open InternalTagArithmeticSyntaxProof (z zRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalRecursionGraphStepSyntaxProof

theorem nonzeroRetained (raw out d k tag : InternalGraphComposition.OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 rawTag tag raw)))
    (hn : Nonempty (Derivation body Delta (equal tag (numeral 0)).not))
    (ha : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) z raw)))
    (ho : Nonempty (Derivation body Delta (graph3 eraseRaw out d k raw))) :
    Nonempty (Derivation body Delta (eqn out raw)) := by
  simpa only [UnchangedLeafResult,equalEqn] using
    nonzeroLeafForward .erase out d k raw tag ht hn (leafForward .erase d k raw out ha ho)

theorem leafCommute (raw a b i j upper lower left right : InternalGraphComposition.OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) z raw)))
    (ho : Nonempty (Derivation body Delta (ltF i (suc j))))
    (hu : Nonempty (Derivation body Delta (graph3 eraseRaw upper b (suc j) raw)))
    (hl : Nonempty (Derivation body Delta (graph3 eraseRaw left a i upper)))
    (hd : Nonempty (Derivation body Delta (graph3 eraseRaw lower a i raw)))
    (hr : Nonempty (Derivation body Delta (graph3 eraseRaw right b j lower))) : Nonempty (Derivation body Delta (equal left right)) := by
  apply programCases rawTag (Fin.cons raw Fin.elim0) _
  intro beta r Theta tag hh ht
  simp only [equalEqn, InternalTagArithmeticSyntaxProof.eqnRelabel]
  simp only [consTermRename,emptyRename] at ht
  have ha' := renameInto ha r Theta hh
  have ho' := renameInto ho r Theta hh
  have hu' := renameInto hu r Theta hh
  have hl' := renameInto hl r Theta hh
  have hd' := renameInto hd r Theta hh
  have hr' := renameInto hr r Theta hh
  simp only [graph1Rename, graph3Rename, orderRename, sucRelabel, zRelabel] at ha' ho' hu' hl' hd' hr'
  apply formulaCases (equal tag (numeral 0))
  · have he : Nonempty (Derivation body (equal tag (numeral 0) :: Theta) (eqn tag (numeral 0))) := by
      simpa only [equalEqn] using (show Nonempty (Derivation body (equal tag (numeral 0) :: Theta)
        (equal tag (numeral 0))) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
    have ht0 := outputTransport rawTag tag (numeral 0) (Fin.cons (raw.relabel r) Fin.elim0) he (withHyp ht _)
    apply variableCases (raw.relabel r) _ ht0
    intro gamma q Xi index hq hv
    simp only [InternalTagArithmeticSyntaxProof.eqnRelabel]
    have ho'' := renameInto (withHyp ho' (equal tag (numeral 0))) q Xi hq
    have hu'' := renameInto (withHyp hu' (equal tag (numeral 0))) q Xi hq
    have hl'' := renameInto (withHyp hl' (equal tag (numeral 0))) q Xi hq
    have hd'' := renameInto (withHyp hd' (equal tag (numeral 0))) q Xi hq
    have hr'' := renameInto (withHyp hr' (equal tag (numeral 0))) q Xi hq
    simp only [graph3Rename,orderRename,sucRelabel] at ho'' hu'' hl'' hd'' hr''
    simpa only [equalEqn] using OriginalTwoDeletionInternalVariableProof.variableCommute
      ((raw.relabel r).relabel q) index ((a.relabel r).relabel q) ((b.relabel r).relabel q)
      ((i.relabel r).relabel q) ((j.relabel r).relabel q) ((upper.relabel r).relabel q)
      ((lower.relabel r).relabel q) ((left.relabel r).relabel q) ((right.relabel r).relabel q)
      hv ho'' hu'' hl'' hd'' hr''
  · have hn : Nonempty (Derivation body ((equal tag (numeral 0)).not :: Theta)
        (equal tag (numeral 0)).not) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have eu := nonzeroRetained (raw.relabel r) (upper.relabel r) (b.relabel r) (suc (j.relabel r)) tag
      (withHyp ht _) hn (withHyp ha' _) (withHyp hu' _)
    have ed := nonzeroRetained (raw.relabel r) (lower.relabel r) (a.relabel r) (i.relabel r) tag
      (withHyp ht _) hn (withHyp ha' _) (withHyp hd' _)
    have el := thirdInputTransport (Delta := (equal tag (numeral 0)).not :: Theta) eraseRaw (left.relabel r) (a.relabel r) (i.relabel r)
      (upper.relabel r) (raw.relabel r) (by simpa only [equalEqn] using eu) (withHyp hl' _)
    have er := thirdInputTransport (Delta := (equal tag (numeral 0)).not :: Theta) eraseRaw (right.relabel r) (b.relabel r) (j.relabel r)
      (lower.relabel r) (raw.relabel r) (by simpa only [equalEqn] using ed) (withHyp hr' _)
    obtain ⟨el⟩ := nonzeroRetained (raw.relabel r) (left.relabel r) (a.relabel r) (i.relabel r) tag
      (withHyp ht _) hn (withHyp ha' _) el
    obtain ⟨er⟩ := nonzeroRetained (raw.relabel r) (right.relabel r) (b.relabel r) (j.relabel r) tag
      (withHyp ht _) hn (withHyp ha' _) er
    exact ⟨trans el (symm er)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalLeafProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalLeafProof
