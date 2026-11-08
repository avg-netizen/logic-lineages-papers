module
public import LogicLineages.Audit
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedNumericIterationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumericIterationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedNumericIterationSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalParameterizedNumericIteration InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalRecursionGraphStepSyntaxProof InternalGraphCompositionTotalityProof InternalRecursionClosureProof
open InternalGraphCompositionFunctionalityProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

@[simp] theorem parameterRepeatRename {β : Type} (P : Program 2)
    (out count value parameter : OTerm α) (j : α → β) :
    (repeatGraph P out count value parameter).relabel j =
      repeatGraph P (out.relabel j) (count.relabel j) (value.relabel j) (parameter.relabel j) := by
  simp only [repeatGraph,programRename,consTermRename,emptyRename]

/-- Simultaneously obtain actual pair graphs at one unchanged parameter.
All witnesses come from existing program totality inside the calculus. -/
theorem pairValuesCases {n : Nat} (parameter : OTerm α) (values : Fin n → OTerm α)
    (psi : Formula α)
    (k : ∀ (β : Type) (j : α → β) (Delta : List (Formula β)) (states : Fin n → OTerm β),
      (∀ r ∈ Gamma, r.relabel j ∈ Delta) →
      (∀ i, Nonempty (Derivation body Delta
        (graph2 InternalPairing.pairing (states i) (parameter.relabel j) ((values i).relabel j)))) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  let qs : Fin n → Program (n+1) := fun i =>
    pairOf (.projection 0) (.projection i.succ)
  apply supplyOutputs body (n+1) n (fun i => OrdinaryArithmetic.graphFormula (qs i))
    (fun i => (actualOriginalPrograms body (n+1) (qs i)).1)
    α Gamma (Fin.cons parameter values) psi
  intro β j Delta states hj hs
  apply k β j Delta states hj
  intro i
  let xs : Fin (n+1) → OTerm β := Fin.cons (parameter.relabel j) (fun a => (values a).relabel j)
  have hsi : Nonempty (Derivation body Delta (programGraph (qs i) (states i) xs)) := by
    simpa only [xs,programGraph,consTermRename] using hs i
  exact binaryRecover InternalPairing.pairing (.projection 0) (.projection i.succ)
    (states i) (parameter.relabel j) ((values i).relabel j) xs hsi
    (projectionValue 0 xs) (projectionValue i.succ xs)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedNumericIterationSyntaxProof

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedNumericIterationSyntaxProof
