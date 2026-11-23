module
public import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAuxiliaryRefinementASTProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchControlChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeObjectControlProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAuxiliarySameFieldProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCases compositionRecover)
open ID1Completion.InternalControlGraphSupportProof (programRename projectionValue outputTransport)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestProof (equalityOfAcceptance)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalFreshProbeDispatchControlChecks (exact_DispatchControlAST)
open NumberedWindowInternalAtomicApplicationShapeObjectControlProof (callSlot)
open NumberedWindowInternalAtomicRefinement (atSource atTarget)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalNeutralAuxiliaryRefinement (sameField)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem fromTargetSlot (p : Program 1) (x w y t : OTerm α)
    (held : Nonempty (Derivation B Γ (programGraph (atTarget p) t ![x,w,y]))) :
    Nonempty (Derivation B Γ (unary p t y)) := by
  unfold atTarget at held
  apply compositionRecover p (fun _ : Fin 1 => .projection (2 : Fin 3)) t ![x,w,y] ![y] held
  intro k
  obtain rfl := Fin.eq_zero k
  exact projectionValue 2 ![x,w,y]

/-- Recover the real target selector at the same known value. This uses
functionality and the original comparison of the two physical calls. -/
theorem exact_OpenSameFieldTarget (p : Program 1) (x w y a : OTerm α)
    (source : Nonempty (Derivation B Γ (unary p a x)))
    (compared : Nonempty (Derivation B Γ (programGraph (sameField p) (suc z) ![x,w,y]))) :
    Nonempty (Derivation B Γ (unary p a y)) := by
  apply programCases (atTarget p) (![x,w,y] : Fin 3 → OTerm α) (unary p a y)
  intro β j Δ t keep current
  rw [tripleInputsRename] at current
  have known := renameInto source j Δ keep
  rw [unaryRename] at known ⊢
  have c := renameInto compared j Δ keep
  simp only [programRename,tripleInputsRename,sucRelabel,zRelabel] at c
  let now : Fin 3 → OTerm β := ![x.relabel j,w.relabel j,y.relabel j]
  have s : Nonempty (Derivation B Δ (programGraph (atSource p) (a.relabel j) now)) :=
    callSlot p 0 (a.relabel j) now known
  have tests : Nonempty (Derivation B Δ (programGraph equalityTest (suc z) ![a.relabel j,t])) := by
    rw [sameField,exact_DispatchControlAST.2.2.2.1] at c
    exact compositionRecover equalityTest ![atSource p,atTarget p] (suc z) now ![a.relabel j,t]
      c (fun k => Fin.cases s (Fin.cases current (fun q => Fin.elim0 q)) k)
  obtain ⟨e⟩ := equalityOfAcceptance (a.relabel j) t tests
  exact outputTransport p t (a.relabel j) ![y.relabel j] ⟨symm e⟩
    (fromTargetSlot p (x.relabel j) (w.relabel j) (y.relabel j) t current)

#print axioms exact_OpenSameFieldTarget
end LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAuxiliarySameFieldProof
