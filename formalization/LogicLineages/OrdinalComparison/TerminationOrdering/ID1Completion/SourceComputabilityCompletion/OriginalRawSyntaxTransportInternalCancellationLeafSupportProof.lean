module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableCancellationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSelectorsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParametersQueryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalLeafParametersProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellationLeafSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalGraphCompositionEqualityProof InternalSourceInversionSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof
open InternalOriginalPairingOrderArithmeticProof (formulaCases withHyp)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternal
open OriginalRawSyntaxTransportInternalVariableLeafProof OriginalRawSyntaxTransportInternalVariableCancellationProof
open OriginalRawSyntaxTransportInternalConstructorSelectorsProof OriginalRawSyntaxTransportInternalConstructorLeafProof
open OriginalRawSyntaxTransportInternalFoldLeafProof OriginalRawSyntaxTransportInternalParametersQueryProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Equality transport changes only the raw third argument of an actual graph. -/
theorem thirdInputTransport (p : Program 3) (out d k source target : OTerm alpha)
    (he : Nonempty (Derivation body Delta (equal source target)))
    (h : Nonempty (Derivation body Delta (graph3 p out d k source))) :
    Nonempty (Derivation body Delta (graph3 p out d k target)) := by
  apply graphInputTransport body alpha 3 Delta (OrdinaryArithmetic.graphFormula p) out
    (Fin.cons d (Fin.cons k (Fin.cons source Fin.elim0)))
    (Fin.cons d (Fin.cons k (Fin.cons target Fin.elim0))) _ h
  intro i
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun q => Fin.elim0 q))) i
  · rw [onEquality]; exact ⟨refl d⟩
  · rw [onEquality]; exact ⟨refl k⟩
  · exact he

theorem variableLeafRightInverse (raw shifted d k i : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph1 variableConstructor raw i)))
    (hs : Nonempty (Derivation body Delta (graph3 (leaf .shift) shifted (numeral 0) k raw))) :
    Nonempty (Derivation body Delta (graph3 (leaf .erase) raw d k shifted)) := by
  apply ternaryCases (leaf .erase) d k shifted _
  intro beta j Theta erased hj he
  rw [graph3Rename]
  have hr' := renameInto hr j Theta hj
  have hs' := renameInto hs j Theta hj
  rw [graph1Rename] at hr'
  simp only [graph3Rename,numeral,InternalTagArithmeticSyntaxProof.zRelabel] at hs'
  have hs'' := OriginalRawSyntaxTransportInternalLeafParametersProof.shiftLeafParameters
    (shifted.relabel j) (numeral 0) (d.relabel j) (k.relabel j) (raw.relabel j) hs'
  have hc := variableLeafCancellation (raw.relabel j) (shifted.relabel j) erased
    (d.relabel j) (k.relabel j) (i.relabel j) hr' hs'' he
  have hce : Nonempty (Derivation body Theta (eqn erased (raw.relabel j))) := by
    simpa only [equalEqn] using hc
  exact outputTransport (leaf .erase) erased (raw.relabel j)
    (Fin.cons (d.relabel j) (Fin.cons (k.relabel j) (Fin.cons (shifted.relabel j) Fin.elim0))) hce he

theorem shiftedVariableArity (raw shifted k i : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph1 variableConstructor raw i)))
    (hs : Nonempty (Derivation body Delta (graph3 (leaf .shift) shifted (numeral 0) k raw))) :
    Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) z shifted)) := by
  apply formulaCases (InternalLessThan.strictLess i k)
  · have hl : Nonempty (Derivation body (InternalLessThan.strictLess i k :: Delta)
        (InternalLessThan.strictLess i k)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hv := shiftLeafForwardAt raw shifted (numeral 0) k i i (withHyp hr _)
      (shiftChoiceBelow raw (numeral 0) k i (withHyp hr _) hl) (withHyp hs _)
    exact variableArity (.projection 0) shifted i (Fin.cons shifted Fin.elim0)
      (projectionValue 0 (Fin.cons shifted Fin.elim0)) hv
  · have hn : Nonempty (Derivation body ((InternalLessThan.strictLess i k).not :: Delta)
        (InternalLessThan.strictLess i k).not) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hv := shiftLeafForwardAt raw shifted (numeral 0) k i (suc i) (withHyp hr _)
      (shiftChoiceNotBelow raw (numeral 0) k i (withHyp hr _) hn) (withHyp hs _)
    exact variableArity (.projection 0) shifted (suc i) (Fin.cons shifted Fin.elim0)
      (projectionValue 0 (Fin.cons shifted Fin.elim0)) hv

/-- A variable's full original bounded folds already cancel internally. -/
theorem variableFoldRightInverse (raw shifted d k i : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph1 variableConstructor raw i)))
    (hs : Nonempty (Derivation body Delta (graph3 (fold .shift) shifted (numeral 0) k raw))) :
    Nonempty (Derivation body Delta (graph3 (fold .erase) raw d k shifted)) := by
  have ha := variableArity (.projection 0) raw i (Fin.cons raw Fin.elim0)
    (projectionValue 0 (Fin.cons raw Fin.elim0)) hr
  have hl := leafForward .shift (numeral 0) k raw shifted ha hs
  exact leafBackward .erase d k shifted raw (shiftedVariableArity raw shifted k i hr hl)
    (variableLeafRightInverse raw shifted d k i hr hl)

/-- Every nonzero-tag zero-arity leaf is retained literally, including
malformed tag six and tags outside the eight constructors. -/
theorem nonzeroLeafFoldRightInverse (raw shifted d k tag : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 rawTag tag raw)))
    (hn : Nonempty (Derivation body Delta (equal tag (numeral 0)).not))
    (ha : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) z raw)))
    (hs : Nonempty (Derivation body Delta (graph3 (fold .shift) shifted (numeral 0) k raw))) :
    Nonempty (Derivation body Delta (graph3 (fold .erase) raw d k shifted)) := by
  have he := nonzeroLeafForward .shift shifted (numeral 0) k raw tag ht hn
    (leafForward .shift (numeral 0) k raw shifted ha hs)
  have ho : Nonempty (Derivation body Delta (UnchangedLeafResult .erase raw raw)) := by
    simpa only [UnchangedLeafResult,equalEqn] using
      (show Nonempty (Derivation body Delta (eqn raw raw)) from ⟨refl raw⟩)
  have hg := leafBackward .erase d k raw raw ha (nonzeroLeafBackward .erase raw d k raw tag ht hn ho)
  have he' : Nonempty (Derivation body Delta (eqn shifted raw)) := by
    simpa only [UnchangedLeafResult,equalEqn] using he
  obtain ⟨he'⟩ := he'
  apply thirdInputTransport (fold .erase) raw d k raw shifted _ hg
  simpa only [equalEqn] using (Nonempty.intro (symm he'))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellationLeafSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellationLeafSupportProof
