module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellationLeafSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellationLeafProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z eqn zRelabel)
open InternalOriginalPairingOrderArithmeticProof (formulaCases withHyp)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalVariableSupportProof
open OriginalRawSyntaxTransportInternalCancellationLeafSupportProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Every raw natural with tag zero is the original variable constructor.
The index is supplied internally by total unpair, not by a source-domain premise. -/
theorem variableCases (raw : OTerm alpha) (psi : Formula alpha)
    (ht : Nonempty (Derivation body Delta (graph1 rawTag (numeral 0) raw)))
    (step : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (i : OTerm beta),
      (∀ r ∈ Delta, r.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph1 variableConstructor (raw.relabel j) i)) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  apply programCases InternalUnpair.right (Fin.cons raw Fin.elim0) _
  intro beta j Theta i hj hi
  simp only [consTermRename,emptyRename] at hi
  have ht' := renameInto ht j Theta hj
  simp only [graph1Rename,numeral,zRelabel] at ht'
  exact step beta j Theta i hj (variableConstructorValue (raw.relabel j) i
    (reconstructPair (raw.relabel j) (numeral 0) i ht' hi))

/-- Zero-arity cancellation covers every raw input, including all malformed
and unknown-tag leaves. No typing, source code or native premise is used. -/
theorem leafFoldRightInverse (raw shifted d k : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) z raw)))
    (hs : Nonempty (Derivation body Delta (graph3 (fold .shift) shifted (numeral 0) k raw))) :
    Nonempty (Derivation body Delta (graph3 (fold .erase) raw d k shifted)) := by
  apply programCases rawTag (Fin.cons raw Fin.elim0) _
  intro beta j Theta tag hj ht
  rw [graph3Rename]
  simp only [consTermRename,emptyRename] at ht
  have ha' := renameInto ha j Theta hj
  have hs' := renameInto hs j Theta hj
  simp only [graph1Rename,graph3Rename,numeral,zRelabel] at ha' hs'
  apply formulaCases (equal tag (numeral 0))
  · have he : Nonempty (Derivation body (equal tag (numeral 0) :: Theta) (eqn tag (numeral 0))) := by
      simpa only [equalEqn] using
        (show Nonempty (Derivation body (equal tag (numeral 0) :: Theta) (equal tag (numeral 0))) from
          ⟨Derivation.hypothesis List.mem_cons_self⟩)
    have ht0 := outputTransport rawTag tag (numeral 0) (Fin.cons (raw.relabel j) Fin.elim0) he (withHyp ht _)
    apply variableCases (raw.relabel j) _ ht0
    intro gamma l Xi i hl hv
    rw [graph3Rename]
    have hs'' := renameInto (withHyp hs' (equal tag (numeral 0))) l Xi hl
    simp only [graph3Rename,numeral,zRelabel] at hs''
    exact variableFoldRightInverse ((raw.relabel j).relabel l) ((shifted.relabel j).relabel l)
      ((d.relabel j).relabel l) ((k.relabel j).relabel l) i hv hs''
  · exact nonzeroLeafFoldRightInverse (raw.relabel j) (shifted.relabel j) (d.relabel j) (k.relabel j)
      tag (withHyp ht _) ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp ha' _) (withHyp hs' _)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellationLeafProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellationLeafProof
