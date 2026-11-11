module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableSpecProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableActionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternal OriginalRawSyntaxTransportInternalTargets
open OriginalRawSyntaxTransportInternalVariableSupportProof
open OriginalRawSyntaxTransportInternalVariableSpecSyntaxProof
open OriginalRawSyntaxTransportInternalVariableSpecProof

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- The raw constructor witness is supplied internally by original Program
totality and eliminated before returning the exact literal branch formula. -/
theorem variableActionSpecForward (mode : Mode) (out d k i : OTerm alpha)
    (h : Nonempty (Derivation body Delta (graph3 (variableAction mode) out d k i))) :
    Nonempty (Derivation body Delta (VariableSpec mode out d k i)) := by
  apply programCases variableConstructor (Fin.cons i Fin.elim0) _
  intro beta j Theta raw hj hr
  rw [variableSpecRename]
  simp only [consTermRename,emptyRename] at hr
  have h' := renameInto h j Theta hj
  rw [graph3Rename] at h'
  exact variableLeafSpecForward mode raw (out.relabel j) (d.relabel j) (k.relabel j) (i.relabel j) hr
    (variableActionForward mode raw (out.relabel j) (d.relabel j) (k.relabel j) (i.relabel j) hr h')

theorem variableActionSpecBackward (mode : Mode) (out d k i : OTerm alpha)
    (h : Nonempty (Derivation body Delta (VariableSpec mode out d k i))) :
    Nonempty (Derivation body Delta (graph3 (variableAction mode) out d k i)) := by
  apply programCases variableConstructor (Fin.cons i Fin.elim0) _
  intro beta j Theta raw hj hr
  rw [graph3Rename]
  simp only [consTermRename,emptyRename] at hr
  have h' := renameInto h j Theta hj
  rw [variableSpecRename] at h'
  exact variableActionBackward mode raw (out.relabel j) (d.relabel j) (k.relabel j) (i.relabel j) hr
    (variableLeafSpecBackward mode raw (out.relabel j) (d.relabel j) (k.relabel j) (i.relabel j) hr h')

/-- All three literal variable actions hold for arbitrary positive bodies,
logical contexts and symbolic indices. Strict comparisons, exact equality and
predecessor witnesses are derived in the original arithmetic calculus. -/
theorem actualRawSyntaxInternalVariableAction : ActualRawSyntaxInternalVariableAction := by
  intro positive mode alpha Delta out d k i
  let A := graph3 (variableAction mode) out d k i
  let B := VariableSpec mode out d k i
  obtain ⟨hf⟩ := variableActionSpecForward (body := positive) (Delta := A :: Delta) mode out d k i
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := variableActionSpecBackward (body := positive) (Delta := B :: Delta) mode out d k i
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableActionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableActionProof
