module
public import LogicLineages.PersistentMarking.NumberedWindowInternalParameterizedPositiveFoldOpenLoopProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationSuccessorProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalParameterizedPositiveFoldOpenLoopReadProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename valueUnique outputTransport)
open ID1Completion.InternalRecursionGraphSuccessorIntroductionProof (recursionSuccessorIntroduction)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (suc)
open NumberedWindowInternalSparsePositiveFold (initial)
open NumberedWindowInternalSparsePositiveFoldOpenSyntaxProof (call6 callRename selectedRename)
open NumberedWindowInternalSparsePositiveIterationSuccessorProof (loopArgs loopArgsRename)
open NumberedWindowInternalParameterizedPositiveFold
open NumberedWindowInternalParameterizedPositiveFoldOpenLoopProof

private theorem loopRename {α β : Type} (A : Program 4) (out fuel c ty start cert : OTerm α) (j : α → β) :
    (loopAt A out fuel c ty start cert).relabel j =
      loopAt A (out.relabel j) (fuel.relabel j) (c.relabel j) (ty.relabel j)
        (start.relabel j) (cert.relabel j) := by
  change (programGraph (iterateAt A) out (loopArgs fuel c ty start cert)).relabel j = _
  rw [programRename,loopArgsRename] <;> rfl

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem moved {β : Type} (j : α → β) (Δ : List (Formula β))
    (hJ : ∀ p ∈ Γ, p.relabel j ∈ Δ) (A : Program 4) (out fuel c ty start cert : OTerm α)
    (known : Nonempty (Derivation body Γ (loopAt A out fuel c ty start cert))) :
    Nonempty (Derivation body Δ (loopAt A (out.relabel j) (fuel.relabel j)
      (c.relabel j) (ty.relabel j) (start.relabel j) (cert.relabel j))) := by
  have next := renameInto known j Δ hJ
  rw [loopRename] at next
  exact next

/-- Recover the actual selected successor step from two consecutive
open recursion reports. Uses same-body uniqueness, not a numeric fit. -/
theorem exact_OpenParameterizedLoopStepRead (A : Program 4) (out prior fuel c ty start cert : OTerm α)
    (before : Nonempty (Derivation body Γ (loopAt A prior fuel c ty start cert)))
    (after : Nonempty (Derivation body Γ (loopAt A out (suc fuel) c ty start cert))) :
    Nonempty (Derivation body Γ (programGraph (stepAt A) out (call6 fuel prior c ty start cert))) := by
  apply programCases (stepAt A) (call6 fuel prior c ty start cert) _
  intro β j Δ result hJ proposal
  rw [selectedRename]
  rw [callRename] at proposal
  let f' := fuel.relabel j
  let c' := c.relabel j
  let t' := ty.relabel j
  let init' := start.relabel j
  let cert' := cert.relabel j
  let prior' := prior.relabel j
  have prev := moved j Δ hJ A prior fuel c ty start cert before
  have actual := moved j Δ hJ A out (suc fuel) c ty start cert after
  rw [sucRelabel] at actual
  have composed : Nonempty (Derivation body Δ (loopAt A result (suc f') c' t' init' cert')) :=
    recursionSuccessorIntroduction Δ (OrdinaryArithmetic.graphFormula initial)
      (OrdinaryArithmetic.graphFormula (stepAt A)) result f' prior' ![c',t',init',cert'] prev proposal
  have eq := valueUnique (iterateAt A) result (out.relabel j)
    (loopArgs (suc f') c' t' init' cert') composed actual
  exact outputTransport (stepAt A) result (out.relabel j) (call6 f' prior' c' t' init' cert') eq proposal

#print axioms exact_OpenParameterizedLoopStepRead
end LogicLineages.PersistentMarking.NumberedWindowInternalParameterizedPositiveFoldOpenLoopReadProof
