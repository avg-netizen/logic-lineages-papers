module
public import LogicLineages.Audit
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedNumericIterationSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedNumericIterationPreservationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedNumericIterationBridgeProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalParameterizedNumericIteration InternalParameterizedNumericIterationSyntaxProof
open InternalParameterizedNumericIterationPreservationProof
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalRecursionGraphStepSyntaxProof InternalGraphCompositionFunctionalityProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- The exact initializer subexpression of the frozen ternary AST. -/
def initialPair : Program 3 :=
  .composition InternalPairing.pairing
    (Fin.cons (.projection (2 : Fin 3)) (Fin.cons (.projection (1 : Fin 3)) Fin.elim0))

/-- The exact carried-run subexpression before the final right projection. -/
def carriedRepeat (P : Program 2) : Program 3 :=
  .composition (InternalNumericIteration.repeatProgram (carryP P))
    (Fin.cons (.projection (0 : Fin 3)) (Fin.cons initialPair Fin.elim0))

theorem initialValue (count value parameter initial : OTerm α)
    (hi : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing initial parameter value))) :
    Nonempty (Derivation body Gamma (graph3 initialPair initial count value parameter)) := by
  exact binaryValue InternalPairing.pairing (.projection 2) (.projection 1)
    initial parameter value (Fin.cons count (Fin.cons value (Fin.cons parameter Fin.elim0))) hi
    (projectionValue 2 (Fin.cons count (Fin.cons value (Fin.cons parameter Fin.elim0))))
    (projectionValue 1 (Fin.cons count (Fin.cons value (Fin.cons parameter Fin.elim0))))

theorem iterationValue (P : Program 2) (count value parameter initial final : OTerm α)
    (hi : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing initial parameter value)))
    (hr : Nonempty (Derivation body Gamma
      (InternalNumericIteration.repeatGraph (carryP P) final count initial))) :
    Nonempty (Derivation body Gamma (graph3 (carriedRepeat P) final count value parameter)) := by
  exact binaryValue (InternalNumericIteration.repeatProgram (carryP P)) (.projection 0) initialPair
    final count initial (Fin.cons count (Fin.cons value (Fin.cons parameter Fin.elim0))) hr
    (projectionValue 0 (Fin.cons count (Fin.cons value (Fin.cons parameter Fin.elim0))))
    (initialValue count value parameter initial hi)

/-- Pass an actual carried run and both actual pair graphs through the
unchanged initializer/iterator/right-unpair composition. -/
theorem runValue (P : Program 2) (out count value parameter initial final : OTerm α)
    (hi : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing initial parameter value)))
    (hf : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing final parameter out)))
    (hr : Nonempty (Derivation body Gamma
      (InternalNumericIteration.repeatGraph (carryP P) final count initial))) :
    Nonempty (Derivation body Gamma (repeatGraph P out count value parameter)) := by
  exact unaryValue InternalUnpair.right (carriedRepeat P) out final
    (Fin.cons count (Fin.cons value (Fin.cons parameter Fin.elim0)))
    (pairRight final parameter out hf) (iterationValue P count value parameter initial final hi hr)

theorem runRight (P : Program 2) (out count value parameter initial final : OTerm α)
    (hi : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing initial parameter value)))
    (hr : Nonempty (Derivation body Gamma
      (InternalNumericIteration.repeatGraph (carryP P) final count initial)))
    (hp : Nonempty (Derivation body Gamma (repeatGraph P out count value parameter))) :
    Nonempty (Derivation body Gamma (graph1 InternalUnpair.right out final)) := by
  exact unaryRecover InternalUnpair.right (carriedRepeat P) out final
    (Fin.cons count (Fin.cons value (Fin.cons parameter Fin.elim0))) hp
    (iterationValue P count value parameter initial final hi hr)

/-- Recover the complete carried output, not merely its right coordinate.
The missing coordinate is obtained from the internal preservation theorem,
then the original reverse pair inverse and graph functionality identify it. -/
theorem runRecover (P : Program 2) (out count value parameter initial final : OTerm α)
    (hi : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing initial parameter value)))
    (hf : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing final parameter out)))
    (hp : Nonempty (Derivation body Gamma (repeatGraph P out count value parameter))) :
    Nonempty (Derivation body Gamma
      (InternalNumericIteration.repeatGraph (carryP P) final count initial)) := by
  apply programCases (InternalNumericIteration.repeatProgram (carryP P))
    (Fin.cons count (Fin.cons initial Fin.elim0)) _
  intro β j Delta result hj hr
  rw [InternalNumericIterationSyntaxProof.repeatRename]
  simp only [consTermRename,emptyRename] at hr
  have hi' := renameInto hi j Delta hj
  have hf' := renameInto hf j Delta hj
  have hp' := renameInto hp j Delta hj
  simp only [graph2Rename] at hi' hf'
  rw [parameterRepeatRename] at hp'
  have hl := preserveParameter P result (count.relabel j) (initial.relabel j) (parameter.relabel j)
    (pairLeft (initial.relabel j) (parameter.relabel j) (value.relabel j) hi') hr
  have hright := runRight P (out.relabel j) (count.relabel j) (value.relabel j)
    (parameter.relabel j) (initial.relabel j) result hi' hr hp'
  have he := valueUnique InternalPairing.pairing result (final.relabel j)
    (Fin.cons (parameter.relabel j) (Fin.cons (out.relabel j) Fin.elim0))
    (reconstructPair result (parameter.relabel j) (out.relabel j) hl hright) hf'
  exact outputTransport (InternalNumericIteration.repeatProgram (carryP P)) result (final.relabel j)
    (Fin.cons (count.relabel j) (Fin.cons (initial.relabel j) Fin.elim0)) he hr

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedNumericIterationBridgeProof

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedNumericIterationBridgeProof
