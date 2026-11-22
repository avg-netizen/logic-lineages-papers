module

public import LogicLineages.PersistentMarking.NumberedWindowInternalStrictAuxWindowParentTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeaderFieldsTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalStrictAuxWindowHeaderTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseFieldCell (cellTail)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (Reports)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalAuxWindowOpenTargets (windowGraph)
open NumberedWindowInternalCoverSelectedValidityTargets (headerAt)
open NumberedWindowInternalStrictAuxWindowTargets

/-- The input type is not assumed equal to the codomain stored in the node.
The actual selected nonzero result at this literal key determines it. -/
def ExactOpenStrictAuxWindowResultType : Prop :=
  ∀ (base : Program 2) (T : Program 1) (body : Positive (Fin 1)) (α : Type)
    (Γ : List (Formula α)) (ctx ty dom cod fn arg : OTerm α),
    Nonempty (Derivation body Γ
      (windowGraph (strictAuxWindow base T) ctx ty (auxiliaryTerm dom cod fn arg))) →
    Nonempty (Derivation body Γ (eqn ty cod))

/-- At an arbitrary raw key with a genuine original tag-six header report,
retain the ordered physical field witnesses and the same raw packing
equation. The physical stored codomain agrees with the supplied type by
an object derivation, not by an extra equality premise. -/
def ExactOpenStrictAuxWindowAtHeader : Prop :=
  ∀ (base : Program 2) (T : Program 1) (body : Positive (Fin 1)) (α : Type)
    (Γ : List (Formula α)) (ctx ty raw : OTerm α) (goal : Formula α),
    Nonempty (Derivation body Γ (windowGraph (strictAuxWindow base T) ctx ty raw)) →
    Nonempty (Derivation body Γ (headerAt 6 4 raw)) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (dom cod fn arg : OTerm β),
      (∀ p ∈ Γ, p.relabel j ∈ Δ) →
      Reports body Δ (raw.relabel j) cellTail [dom,cod,fn,arg] →
      Nonempty (Derivation body Δ (eqn (raw.relabel j) (auxiliaryTerm dom cod fn arg))) →
      Nonempty (Derivation body Δ (eqn (ty.relabel j) cod)) →
      Nonempty (Derivation body Δ (strictAuxChildren base T (ctx.relabel j) dom cod fn arg)) →
      Nonempty (Derivation body Δ (goal.relabel j))) →
    Nonempty (Derivation body Γ goal)

end LogicLineages.PersistentMarking.NumberedWindowInternalStrictAuxWindowHeaderTargets
