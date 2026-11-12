module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalLeafProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalErasureLeafProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalRawSyntaxTransport
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open InternalOriginalOrderSyntaxProof (ltF orderRename)
open InternalOriginalPairingOrderArithmeticProof (withHyp formulaCases)
open OriginalTwoDeletionInternalVariableArithmeticProof (compareCases)
open OriginalRawSyntaxTransportInternalConstructorSelectorsProof
open OriginalRawSyntaxTransportInternalVariableEraseLeafProof
open OriginalRawSyntaxTransportInternalCancellationLeafProof (variableCases)
open SourceComputabilityFormulaSupportProof (numeral)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem variableArityAfter (raw out d k index : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph1 variableConstructor raw index)))
    (he : Nonempty (Derivation body Delta (graph3 eraseRaw out d k raw))) :
    Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) z out)) := by
  have hl := OriginalRawSyntaxTransportInternalFoldLeafProof.leafForward .erase d k raw out
    (variableArity (.projection 0) raw index ![raw] (projectionValue 0 ![raw]) hv) he
  apply compareCases index k
  · exact variableArity (.projection 0) out index ![out] (projectionValue 0 ![out])
      (eraseLeafBelowForward raw out d k index (withHyp hv _) ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hl _))
  · have heq : Nonempty (Derivation body (eqn index k :: Delta) (equal index k)) := by
      simpa only [equalEqn] using (show Nonempty (Derivation body (eqn index k :: Delta) (eqn index k)) from
        ⟨Derivation.hypothesis List.mem_cons_self⟩)
    exact bottomArity (.projection 0) out d ![out] (projectionValue 0 ![out])
      (eraseLeafEqualForward raw out d k index (withHyp hv _) heq (withHyp hl _))
  · have hg : Nonempty (Derivation body (ltF k index :: Delta) (ltF k index)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    apply programCases InternalEqualityTest.predecessor (Fin.cons index Fin.elim0) _
    intro beta j Theta previous hj hp
    simp only [graph1Rename,zRelabel]
    simp only [consTermRename,emptyRename] at hp
    have hv' := renameInto (withHyp hv (ltF k index)) j Theta hj
    have hl' := renameInto (withHyp hl (ltF k index)) j Theta hj
    have hg' := renameInto hg j Theta hj
    simp only [graph1Rename,graph3Rename,orderRename] at hv' hl' hg'
    exact variableArity (.projection 0) (out.relabel j) previous ![out.relabel j]
      (projectionValue 0 ![out.relabel j])
      (eraseLeafAboveForwardAt (raw.relabel j) (out.relabel j) (d.relabel j) (k.relabel j)
        (index.relabel j) previous hv' hg' hp hl')

theorem leafArityAfter (raw out d k : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) z raw)))
    (he : Nonempty (Derivation body Delta (graph3 eraseRaw out d k raw))) :
    Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) z out)) := by
  apply programCases rawTag (Fin.cons raw Fin.elim0) _
  intro beta j Theta tag hj ht
  simp only [graph1Rename,zRelabel]
  simp only [consTermRename,emptyRename] at ht
  have ha' := renameInto ha j Theta hj
  have he' := renameInto he j Theta hj
  simp only [graph1Rename,graph3Rename,zRelabel] at ha' he'
  apply formulaCases (equal tag (numeral 0))
  · have eq0 : Nonempty (Derivation body (equal tag (numeral 0) :: Theta) (eqn tag (numeral 0))) := by
      simpa only [equalEqn] using (show Nonempty (Derivation body (equal tag (numeral 0) :: Theta)
        (equal tag (numeral 0))) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
    have ht0 := outputTransport rawTag tag (numeral 0) ![raw.relabel j] eq0 (withHyp ht _)
    apply variableCases (raw.relabel j) _ ht0
    intro gamma r Xi index hr hv
    simp only [graph1Rename,zRelabel]
    have he'' := renameInto (withHyp he' (equal tag (numeral 0))) r Xi hr
    rw [graph3Rename] at he''
    exact variableArityAfter ((raw.relabel j).relabel r) ((out.relabel j).relabel r)
      ((d.relabel j).relabel r) ((k.relabel j).relabel r) index hv he''
  · have eq := OriginalTwoDeletionInternalLeafProof.nonzeroRetained (raw.relabel j) (out.relabel j)
      (d.relabel j) (k.relabel j) tag (withHyp ht _) ⟨Derivation.hypothesis List.mem_cons_self⟩
      (withHyp ha' _) (withHyp he' _)
    obtain ⟨eq⟩ := eq
    exact headTransport (arityOf (.projection 0)) z (raw.relabel j) (out.relabel j) Fin.elim0
      ⟨symm eq⟩ (withHyp ha' _)

theorem leafInvariant (raw out d k before after : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) z raw)))
    (he : Nonempty (Derivation body Delta (graph3 eraseRaw out d k raw)))
    (hb : Nonempty (Derivation body Delta (graph1 OriginalStructuralNodeSize.raw before raw)))
    (hh : Nonempty (Derivation body Delta (graph1 OriginalStructuralNodeSize.raw after out))) :
    Nonempty (Derivation body Delta (equal before after)) := by
  obtain ⟨hb1⟩ := valueUnique OriginalStructuralNodeSize.raw before (suc z) ![raw] hb
    (OriginalStructuralNodeSizeInternalLeafProof.leaf raw ha)
  obtain ⟨ha1⟩ := valueUnique OriginalStructuralNodeSize.raw after (suc z) ![out] hh
    (OriginalStructuralNodeSizeInternalLeafProof.leaf out (leafArityAfter raw out d k ha he))
  simpa only [equalEqn] using Nonempty.intro (trans hb1 (symm ha1))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalErasureLeafProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalErasureLeafProof
