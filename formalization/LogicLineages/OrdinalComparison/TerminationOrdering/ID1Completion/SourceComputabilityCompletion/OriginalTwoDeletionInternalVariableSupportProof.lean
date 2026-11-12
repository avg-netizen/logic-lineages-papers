module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellationLeafSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldLeafConstructorsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalVariableSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (eqn z suc)
open InternalTagArithmeticSupportProof
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternal
open OriginalRawSyntaxTransportInternalConstructorSelectorsProof
open OriginalRawSyntaxTransportInternalFoldLeafProof
open OriginalRawSyntaxTransportInternalVariableEraseLeafProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem below (raw out d k x : InternalGraphComposition.OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph1 variableConstructor raw x)))
    (hlt : Nonempty (Derivation body Delta (InternalLessThan.strictLess x k)))
    (ho : Nonempty (Derivation body Delta (graph3 eraseRaw out d k raw))) :
    Nonempty (Derivation body Delta (graph1 variableConstructor out x)) :=
  eraseLeafBelowForward raw out d k x hr hlt
    (leafForward .erase d k raw out
      (variableArity (.projection 0) raw x (Fin.cons raw Fin.elim0)
        (projectionValue 0 (Fin.cons raw Fin.elim0)) hr) ho)

theorem atCutoff (raw out d k : InternalGraphComposition.OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph1 variableConstructor raw k)))
    (ho : Nonempty (Derivation body Delta (graph3 eraseRaw out d k raw))) :
    Nonempty (Derivation body Delta (graph1 bottomConstructor out d)) :=
  eraseLeafEqualForward raw out d k k hr
    (by simpa only [equalEqn] using Nonempty.intro (refl k))
    (leafForward .erase d k raw out
      (variableArity (.projection 0) raw k (Fin.cons raw Fin.elim0)
        (projectionValue 0 (Fin.cons raw Fin.elim0)) hr) ho)

theorem aboveSuccessor (raw out d k x : InternalGraphComposition.OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph1 variableConstructor raw (suc x))))
    (hlt : Nonempty (Derivation body Delta (InternalLessThan.strictLess k (suc x))))
    (ho : Nonempty (Derivation body Delta (graph3 eraseRaw out d k raw))) :
    Nonempty (Derivation body Delta (graph1 variableConstructor out x)) :=
  eraseLeafAboveForwardAt raw out d k (suc x) x hr hlt
    (InternalEqualityTestPredecessorProof.predecessorSuccessor x)
    (leafForward .erase d k raw out
      (variableArity (.projection 0) raw (suc x) (Fin.cons raw Fin.elim0)
        (projectionValue 0 (Fin.cons raw Fin.elim0)) hr) ho)

theorem bottomRetained (raw out d k typ : InternalGraphComposition.OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph1 bottomConstructor raw typ)))
    (ho : Nonempty (Derivation body Delta (graph3 eraseRaw out d k raw))) :
    Nonempty (Derivation body Delta (graph1 bottomConstructor out typ)) := by
  have he := OriginalRawSyntaxTransportInternalFoldLeafConstructorsProof.bottomForward .erase raw out d k typ hr ho
  have he' : Nonempty (Derivation body Delta (eqn out raw)) := by
    simpa only [UnchangedLeafResult,equalEqn] using he
  obtain ⟨he'⟩ := he'
  exact outputTransport bottomConstructor raw out (Fin.cons typ Fin.elim0) ⟨symm he'⟩ hr

theorem sameVariable (left right x : InternalGraphComposition.OTerm alpha)
    (hl : Nonempty (Derivation body Delta (graph1 variableConstructor left x)))
    (hr : Nonempty (Derivation body Delta (graph1 variableConstructor right x))) :
    Nonempty (Derivation body Delta (equal left right)) := by
  simpa only [equalEqn] using valueUnique variableConstructor left right (Fin.cons x Fin.elim0) hl hr

theorem sameBottom (left right typ : InternalGraphComposition.OTerm alpha)
    (hl : Nonempty (Derivation body Delta (graph1 bottomConstructor left typ)))
    (hr : Nonempty (Derivation body Delta (graph1 bottomConstructor right typ))) :
    Nonempty (Derivation body Delta (equal left right)) := by
  simpa only [equalEqn] using valueUnique bottomConstructor left right (Fin.cons typ Fin.elim0) hl hr

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalVariableSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalVariableSupportProof
