module
public import LogicLineages.PersistentMarking.NumberedWindowInternalBetaRootDispatchDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenNodeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalBetaRootDispatchOpenProof

open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open SourceComputabilityFormulaSupportProof (numeral)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchIntro)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelope (nodeGood)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenNodeProof (packedNode)
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (literalGraph)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalBetaRootDispatch

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem witness (src dst : OTerm α) :
    Nonempty (Derivation B Γ (programGraph witnessTest (suc z)
      ![src,rawCons (numeral 6) z,dst])) := by
  let w : OTerm α := rawCons (numeral 6) z
  let xs : Fin 3 → OTerm α := ![src,w,dst]
  have control := (packedNode (body := B) (Γ := Γ) (literal 1 6)
    (numeral 6) [] (literalGraph 6 ![w])).1
  apply compositionValue (nodeGood (literal 1 6) 0)
    (fun _ : Fin 1 => .projection (1 : Fin 3)) (suc z) xs ![w] control
  intro i
  have hi : i = 0 := Fin.eq_zero i
  subst i
  exact projectionValue (1 : Fin 3) xs

/-- Actual original tag-6 empty witness, preserving both raw endpoints.
No assumption identifies the old chosen root AST with this new branch. -/
theorem accept (original : Program 3) (beta : Program 2) (src dst : OTerm α)
    (checked : Nonempty (Derivation B Γ (programGraph beta (suc z) ![src,dst]))) :
    Nonempty (Derivation B Γ (programGraph (root' original beta) (suc z)
      ![src,rawCons (numeral 6) z,dst])) := by
  let xs : Fin 3 → OTerm α := ![src,rawCons (numeral 6) z,dst]
  have call : Nonempty (Derivation B Γ (programGraph (betaCall beta) (suc z) xs)) := by
    apply compositionValue beta ![.projection 0,.projection 2] (suc z) xs ![src,dst] checked
    intro i
    exact Fin.cases (projectionValue (0 : Fin 3) xs)
      (Fin.cases (projectionValue (2 : Fin 3) xs) (fun j => Fin.elim0 j)) i
  exact successorBranchIntro witnessTest original (betaCall beta) (suc z) z xs (witness src dst) call

#print axioms witness
#print axioms accept
end LogicLineages.PersistentMarking.NumberedWindowInternalBetaRootDispatchOpenProof
