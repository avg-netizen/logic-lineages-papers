module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountSupportedTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountTupleProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalControlGraphSupportProof (projectionValue)
open ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserSupportProof (programsCases)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalLiteralCount (entryCount)
open NumberedWindowInternalLiteralCountSupportedTargets (counted)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private def countTape {n : Nat} (needle : OTerm α) (codes : Fin n → OTerm α) :
    Fin (n+1) → OTerm α := Fin.cons needle codes

private def selectCount {n : Nat} (i : Fin n) : Program (n+1) :=
  .composition entryCount ![.projection i.succ,.projection 0]

private theorem countAtIndex {n : Nat} {β : Type} {Δ : List (Formula β)}
    (codes : Fin n → OTerm α) (needle : OTerm α) (j : α → β) (i : Fin n) (out : OTerm β)
    (h : Nonempty (Derivation B Δ (programGraph (selectCount i) out
      (fun a => (countTape needle codes a).relabel j)))) :
    Nonempty (Derivation B Δ (counted ((codes i).relabel j) (needle.relabel j) out)) := by
  let xs : Fin (n+1) → OTerm β := fun a => (countTape needle codes a).relabel j
  apply compositionRecover entryCount ![.projection i.succ,.projection 0] out xs
    ![(codes i).relabel j,needle.relabel j] h
  intro a
  exact Fin.cases (projectionValue i.succ xs)
    (Fin.cases (projectionValue 0 xs) (fun q => Fin.elim0 q)) a

/-- All rows of a given finite tape get actual entryCount graphs at the
same needle. The outputs occur only in the original object-calculus
existential scope, with graph totality/real projections and no semantic
count reflection. This helper does not reorder or deduplicate the input. -/
theorem openCountTuple {n : Nat} (codes : Fin n → OTerm α) (needle : OTerm α) (goal : Formula α)
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (outs : Fin n → OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      (∀ i, Nonempty (Derivation B Δ (counted ((codes i).relabel j) (needle.relabel j) (outs i)))) →
      Nonempty (Derivation B Δ (goal.relabel j))) : Nonempty (Derivation B Γ goal) := by
  apply programsCases selectCount (countTape needle codes) goal
  intro β j Δ outs keep report
  exact next β j Δ outs keep (fun i => countAtIndex codes needle j i (outs i) (report i))

#print axioms openCountTuple
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountTupleProof
