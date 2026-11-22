module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedPairedAuxTargets
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestCompositionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedPairedAuxKernelProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestCompositionProof (equalityOfEqual)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z)
open ID1Completion.InternalTagArithmeticSupportProof (refl)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseCoverScratch (coverOption)
open NumberedWindowInternalSparseScalarEdge (exchangeTape)
open NumberedWindowInternalSparseCoverGuardedExchangeTargets (optionAtSlot compareOptions guardedExchange)
open NumberedWindowInternalCoverCombinedRestrictedPairedAuxTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem swapValue (D : Program 2) (a b : OTerm α)
    (reverse : Nonempty (Derivation body Γ (programGraph D (suc z) ![b,a]))) :
    Nonempty (Derivation body Γ (programGraph (thinSwapExchange D) (suc z) ![a,b])) := by
  apply compositionValue D ![.projection 1,.projection 0] (suc z) ![a,b] ![b,a] reverse
  intro i
  exact Fin.cases (projectionValue 1 ![a,b])
    (Fin.cases (projectionValue 0 ![a,b]) (fun j => Fin.elim0 j)) i

private theorem coverSlot (C : Program 3) (s : Settings) (i : Fin 2) (xs : Fin 2 → OTerm α) (out : OTerm α)
    (h : Nonempty (Derivation body Γ (unary (coverOption C s) out (xs i)))) :
    Nonempty (Derivation body Γ (programGraph (optionAtSlot C s i) out xs)) := by
  apply compositionValue (coverOption C s) (fun _ : Fin 1 => .projection i) out xs ![xs i] h
  intro k
  obtain rfl := Fin.eq_zero k
  exact projectionValue i xs

theorem guardedOfActualPair (C : Program 3) (s : Settings) (D : Program 2) (a b out : OTerm α)
    (ab : Nonempty (Derivation body Γ (programGraph D (suc z) (exchangeTape a b))))
    (ba : Nonempty (Derivation body Γ (programGraph D (suc z) (exchangeTape b a))))
    (ca : Nonempty (Derivation body Γ (unary (coverOption C s) out a)))
    (cb : Nonempty (Derivation body Γ (unary (coverOption C s) out b))) :
    Nonempty (Derivation body Γ (programGraph (guardedExchange C s (thinPairedExchange D))
      (suc z) (exchangeTape a b))) := by
  have pair : Nonempty (Derivation body Γ (programGraph (thinPairedExchange D) (suc z) ![a,b])) :=
    conjunctionAccept D (thinSwapExchange D) ![a,b] ab (swapValue D a b ba)
  have same : Nonempty (Derivation body Γ (programGraph (compareOptions C s) (suc z) ![a,b])) := by
    apply compositionValue equalityTest ![optionAtSlot C s 0,optionAtSlot C s 1]
      (suc z) ![a,b] ![out,out] (equalityOfEqual out out ⟨refl out⟩)
    intro i
    exact Fin.cases (coverSlot C s 0 ![a,b] out ca)
      (Fin.cases (coverSlot C s 1 ![a,b] out cb) (fun k => Fin.elim0 k)) i
  exact conjunctionAccept (thinPairedExchange D) (compareOptions C s) ![a,b] pair same

#print axioms guardedOfActualPair
end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedPairedAuxKernelProof
