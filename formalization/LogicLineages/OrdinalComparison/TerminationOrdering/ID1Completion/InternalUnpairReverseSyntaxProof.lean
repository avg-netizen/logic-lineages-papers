module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairReverseTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairReverseSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram InternalUnpairReverse
open InternalUnpairSupportProof InternalArithmeticProgramsSupportProof InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalAdditionLawsProof
open InternalOriginalOrderSyntaxProof InternalOriginalOrderProof

@[simp] theorem unaryGraphRename {α β : Type} (p : Program 1) (out n : OTerm α) (j : α → β) :
    (unaryGraph p out n).relabel j = unaryGraph p (out.relabel j) (n.relabel j) := by
  simp only [unaryGraph,programRename,InternalRecursionGraphStepSyntaxProof.consTermRename,emptyRename]

@[simp] theorem binaryGraphRename {α β : Type} (p : Program 2) (out x y : OTerm α) (j : α → β) :
    (binaryGraph p out x y).relabel j =
      binaryGraph p (out.relabel j) (x.relabel j) (y.relabel j) := by
  simp only [binaryGraph,programRename,InternalRecursionGraphStepSyntaxProof.consTermRename,emptyRename]

@[simp] theorem boundsRename {α β : Type} (n x y : OTerm α) (j : α → β) :
    (coordinateBounds n x y).relabel j =
      coordinateBounds (n.relabel j) (x.relabel j) (y.relabel j) := by
  change (ltF x (suc n)).relabel j ⊓ (ltF y (suc n)).relabel j = _
  simp only [orderRename,sucRelabel]
  rfl

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- The weak-order witness is obtained by actual strict-order elimination
and cancellation of the two original successor terms. -/
theorem weakOrderCases (Gamma : List (Formula α)) (s t : OTerm α) (psi : Formula α)
    (h : Nonempty (Derivation body Gamma (ltF s (suc t))))
    (k : ∀ (β : Type) (j : α → β) (Delta : List (Formula β)) (w : OTerm β),
      (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (eqn (add (s.relabel j) w) (t.relabel j))) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  apply orderCases Gamma s (suc t) psi h
  intro β j Delta w hj ⟨he⟩
  simp only [sucRelabel] at he
  exact k β j Delta w hj
    ⟨cancelSuc (trans (symm (addSucc (s.relabel j) w)) he)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairReverseSyntaxProof
