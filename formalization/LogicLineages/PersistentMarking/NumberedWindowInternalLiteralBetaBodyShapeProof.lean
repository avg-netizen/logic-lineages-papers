module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBetaLeafOpenProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonBoundOpenRowsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFunctionGuardFieldsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBetaBodyShapeProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open NumberedWindowInternalSparsePathEnvelope (nodeGood)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (packedBody)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof (onTape)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D)
open NumberedWindowInternalLiteralFunctionGuardFieldsProof (nodeAtCases)
open NumberedWindowInternalLiteralBetaLeafProof (rawLambdaShape)
open NumberedWindowInternalLiteralBetaLeafOpenProof (rawLambdaTerm)
open NumberedWindowInternalLiteralSingletonBoundMachineProof (boundShape)
open NumberedWindowInternalLiteralSingletonBoundOpenRowsProof (boundTerm)

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem twoFields (tag : Nat) (q : OTerm α) (goal : Formula α)
    (held : D B Γ (unary (nodeGood (literal 1 tag) 2) (suc z) q))
    (use : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (first second : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      D B Δ (eqn (q.relabel j) (rawCons (numeral tag) (packedBody [first,second]))) →
      D B Δ (goal.relabel j)) : D B Γ goal := by
  apply nodeAtCases tag 2 0 ![q,q,q] goal
    (onTape (nodeGood (literal 1 tag) 2) 0 (suc z) ![q,q,q] held)
  intro β j Δ fields keep size shape _
  rcases fields with _ | ⟨first,_ | ⟨second,_ | ⟨extra,rest⟩⟩⟩ <;> simp at size
  exact use β j Δ first second keep shape

/-- Read the binder and child from an accepted literal lambda shape on the
actual beta body. The fresh fields live in the continuation's context. -/
theorem exact_OpenBetaLambdaBodyShape (body : OTerm α) (goal : Formula α)
    (held : D B Γ (unary rawLambdaShape (suc z) body))
    (use : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (ty child : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      D B Δ (eqn (body.relabel j) (rawLambdaTerm ty child)) → D B Δ (goal.relabel j)) :
    D B Γ goal :=
  twoFields 2 body goal held use

/-- Read the type and index from the accepted bound-node selector at a
body or replacement. The equation names the original tested code. -/
theorem exact_OpenBetaBoundNodeShape (node : OTerm α) (goal : Formula α)
    (held : D B Γ (unary boundShape (suc z) node))
    (use : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (ty index : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      D B Δ (eqn (node.relabel j) (boundTerm ty index)) → D B Δ (goal.relabel j)) :
    D B Γ goal :=
  twoFields 1 node goal held use

#print axioms exact_OpenBetaLambdaBodyShape
#print axioms exact_OpenBetaBoundNodeShape
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBetaBodyShapeProof
