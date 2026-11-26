module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalApplicationNodeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalApplicationAcceptanceProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open OriginalHereditaryValidity OriginalHereditaryValidityInternal OriginalHereditaryValidityInternalRecurrence
open OriginalTransparentLambdaFinalApplicationOutputProof (applicationAcceptanceEquation)
open OriginalTransparentLambdaValidityInternalLambdaSupportProof (addAssumption)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalBetaTotalityProof (addHyp)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem acceptanceAtChildren (s t m node : Program 2) (raw parameter typ fn arg : OTerm alpha)
    (htag : Nonempty (Derivation body Gamma (graph1 OriginalLambdaConstructor.tag (numeral 2) raw)))
    (hnode : Nonempty (Derivation body Gamma
      ((NodeFactors s t m raw parameter).iff (graph2 node (numeral 1) typ parameter))))
    (hchildren : Nonempty (Derivation body Gamma
      ((RootApplicationChildren s t m raw parameter).iff
        (graph2 (validator s t m) (numeral 1) fn parameter ⊓
          graph2 (validator s t m) (numeral 1) arg parameter)))) :
    Nonempty (Derivation body Gamma
      ((graph2 (validator s t m) (numeral 1) raw parameter).iff
        (graph2 node (numeral 1) typ parameter ⊓
          (graph2 (validator s t m) (numeral 1) fn parameter ⊓
            graph2 (validator s t m) (numeral 1) arg parameter)))) := by
  let A := graph2 node (numeral 1) typ parameter ⊓
    (graph2 (validator s t m) (numeral 1) fn parameter ⊓
      graph2 (validator s t m) (numeral 1) arg parameter)
  obtain ⟨he⟩ := applicationAcceptanceEquation s t m raw parameter
    (graph2 node (numeral 1) typ parameter) htag hnode
  obtain ⟨hc⟩ := hchildren
  exact ⟨Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction (by
      have h := Derivation.implicationElimination (addHyp (Derivation.conjunctionLeft he) _)
        (Derivation.hypothesis List.mem_cons_self)
      exact Derivation.conjunctionIntroduction (Derivation.conjunctionLeft h)
        (Derivation.implicationElimination (addHyp (Derivation.conjunctionLeft hc) _)
          (Derivation.conjunctionRight h))))
    (Derivation.implicationIntroduction (by
      have h : Derivation body (A :: Gamma) A := Derivation.hypothesis List.mem_cons_self
      exact Derivation.implicationElimination (addHyp (Derivation.conjunctionRight he) _)
        (Derivation.conjunctionIntroduction (Derivation.conjunctionLeft h)
          (Derivation.implicationElimination (addHyp (Derivation.conjunctionRight hc) _)
            (Derivation.conjunctionRight h)))))⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalApplicationAcceptanceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalApplicationAcceptanceProof
