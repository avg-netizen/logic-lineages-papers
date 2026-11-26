module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonBoundOpenLowerProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonBoundOpenAboveExistenceProof

open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename headTransport valueUnique)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn sucRelabel zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (addSucc)
open ID1Completion.InternalAdditionLawsProof (add)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF orderRename)
open ID1Completion.InternalOriginalOrderProof (orderCases)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open SourceComputabilityFormulaSupportProof (numeral)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename rawConsRename packedBodyRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalFreshProbeDispatchProgram (predOne)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D)
open NumberedWindowInternalLiteralSingletonBoundMachineProof
open NumberedWindowInternalLiteralSingletonBoundOpenRowsProof
open NumberedWindowInternalLiteralSingletonBoundOpenLowerProof
  (exact_OpenPredOneSuccessor exact_OpenSingletonBoundAbovePredecessor)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem numeralRename {β : Type} (n : Nat) (r : α → β) :
    (numeral n : OTerm α).relabel r = numeral n := by
  induction n with
  | zero => exact zRelabel r
  | succ n ih =>
    simpa only [numeral,sucRelabel] using
      congrArg ID1Completion.InternalTagArithmeticSyntaxProof.suc ih

/-- The packed bound node commutes with renaming of free variables. -/
theorem boundTermRename {β : Type} (t i : OTerm α) (r : α → β) :
    (boundTerm t i).relabel r = boundTerm (t.relabel r) (i.relabel r) := by
  simp only [boundTerm,rawConsRename,packedBodyRename,numeralRename,List.map_cons,List.map_nil]

/-- Object-level predecessor availability. From a derivation of `d < i`
(take `d := z` for plain positivity) the original order elimination gives a
gap `w` with `d + suc w = i`; the addition-successor axiom turns this into
`i = suc (d + w)`, and the actual `predOne` graph at `i` follows by input
transport from its successor row. The witness is an object term of the
extended context, never a numeral. -/
theorem exact_OpenPredecessorOfLess (d i : OTerm α) (goal : Formula α)
    (above : D B Γ (ltF d i))
    (use : ∀ (β : Type) (r : α → β) (Δ : List (Formula β)) (j : OTerm β),
      (∀ f ∈ Γ, f.relabel r ∈ Δ) →
      D B Δ (eqn (i.relabel r) (suc j)) →
      D B Δ (unary predOne j (i.relabel r)) →
      D B Δ (goal.relabel r)) : D B Γ goal := by
  apply orderCases Γ d i goal above
  intro β r Δ w keep ⟨gap⟩
  have same : Derivation B Δ (eqn (i.relabel r) (suc (add (d.relabel r) w))) :=
    ID1Completion.InternalTagArithmeticSupportProof.trans
      (ID1Completion.InternalTagArithmeticSupportProof.symm gap) (addSucc (d.relabel r) w)
  have pred : D B Δ (unary predOne (add (d.relabel r) w) (i.relabel r)) :=
    headTransport predOne (add (d.relabel r) w) (suc (add (d.relabel r) w)) (i.relabel r)
      Fin.elim0 ⟨ID1Completion.InternalTagArithmeticSupportProof.symm same⟩
      (exact_OpenPredOneSuccessor (add (d.relabel r) w))
  exact use β r Δ (add (d.relabel r) w) keep ⟨same⟩ pred

/-- Existence of the actual `singletonBound` result on a packed bound node
whose open index is above the depth. No predecessor graph is supplied: the
continuation receives an object term `j` with `i = suc j` and the graph of
the actual program with output `suc (boundTerm t j)`. Both original syntax
guards and the order derivation are transported unchanged into the extended
context. -/
theorem exact_OpenSingletonBoundAboveCases (V : Program 1) (H : Program 2) (U : Program 3)
    (a d t i : OTerm α) (goal : Formula α)
    (inserted : D B Γ (unary V (suc z) a))
    (typedNode : D B Γ (unary V (suc z) (boundTerm t i)))
    (above : D B Γ (ltF d i))
    (use : ∀ (β : Type) (r : α → β) (Δ : List (Formula β)) (j : OTerm β),
      (∀ f ∈ Γ, f.relabel r ∈ Δ) →
      D B Δ (eqn (i.relabel r) (suc j)) →
      D B Δ (programGraph (singletonBound V H U) (suc (boundTerm (t.relabel r) j))
        ![a.relabel r,d.relabel r,boundTerm (t.relabel r) (i.relabel r)]) →
      D B Δ (goal.relabel r)) : D B Γ goal := by
  apply exact_OpenPredecessorOfLess d i goal above
  intro β r Δ j keep same pred
  have inserted' : D B Δ (unary V (suc z) (a.relabel r)) := by
    have moved := renameInto inserted r Δ keep
    rw [unaryRename,sucRelabel,zRelabel] at moved
    exact moved
  have typedNode' : D B Δ (unary V (suc z) (boundTerm (t.relabel r) (i.relabel r))) := by
    have moved := renameInto typedNode r Δ keep
    rw [unaryRename,sucRelabel,zRelabel,boundTermRename] at moved
    exact moved
  have above' : D B Δ (ltF (d.relabel r) (i.relabel r)) := by
    have moved := renameInto above r Δ keep
    rw [orderRename] at moved
    exact moved
  exact use β r Δ j keep same
    (exact_OpenSingletonBoundAbovePredecessor V H U (a.relabel r) (d.relabel r) (t.relabel r)
      (i.relabel r) j inserted' typedNode' above' pred)

/-- Value form for a caller that already holds an output of the actual
program, for example from a composition split: above the depth that output
is provably the lowered node. Functionality of the original program graph
identifies it with the constructed result. -/
theorem exact_OpenSingletonBoundAboveValue (V : Program 1) (H : Program 2) (U : Program 3)
    (a d t i out : OTerm α) (goal : Formula α)
    (inserted : D B Γ (unary V (suc z) a))
    (typedNode : D B Γ (unary V (suc z) (boundTerm t i)))
    (above : D B Γ (ltF d i))
    (computed : D B Γ (programGraph (singletonBound V H U) out ![a,d,boundTerm t i]))
    (use : ∀ (β : Type) (r : α → β) (Δ : List (Formula β)) (j : OTerm β),
      (∀ f ∈ Γ, f.relabel r ∈ Δ) →
      D B Δ (eqn (i.relabel r) (suc j)) →
      D B Δ (eqn (out.relabel r) (suc (boundTerm (t.relabel r) j))) →
      D B Δ (goal.relabel r)) : D B Γ goal := by
  apply exact_OpenSingletonBoundAboveCases V H U a d t i goal inserted typedNode above
  intro β r Δ j keep same graph
  have moved := renameInto computed r Δ keep
  rw [programRename,tripleInputsRename,boundTermRename] at moved
  exact use β r Δ j keep same
    (valueUnique (singletonBound V H U) (out.relabel r) (suc (boundTerm (t.relabel r) j))
      ![a.relabel r,d.relabel r,boundTerm (t.relabel r) (i.relabel r)] moved graph)

#print axioms boundTermRename
#print axioms exact_OpenPredecessorOfLess
#print axioms exact_OpenSingletonBoundAboveCases
#print axioms exact_OpenSingletonBoundAboveValue
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonBoundOpenAboveExistenceProof
