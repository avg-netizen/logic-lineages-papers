module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.InductionBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.PositiveProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.PositiveInductionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc sucRelabel)
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open Continuation20261115 Induction
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem atSuccessor (n : Nat) (fuel : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowFuel n (suc fuel)))) :
    Nonempty (Derivation body Delta (AtFuel n (suc fuel))) := by
  apply InductionBindingProof.atFuelIntro
  unfold matrix
  simp only [sucRelabel]
  apply Nonempty.intro
  apply Derivation.implicationIntroduction
  let v (i : Fin 11) : OTerm (alpha ⊕ Fin 11) := .var (.inr i)
  let f := fuel.relabel (Sum.inl : alpha → alpha ⊕ Fin 11)
  let A : Formula (alpha ⊕ Fin 11) :=
    graph2 InternalPairing.pairing (v 0) (v 6) (suc f) ⊓
      graph2 InternalPairing.pairing (v 1) (v 7) (v 2) ⊓
      graph2 InternalPairing.pairing (v 2) (v 8) (v 3) ⊓
      graph2 InternalPairing.pairing (v 3) (v 9) (v 10) ⊓
      graph2 (OriginalEnumerationRecursion.enumeration n) (v 4) (v 0) (v 1)
  let Theta := A :: Delta.map (fun q => q.relabel (Sum.inl : alpha → alpha ⊕ Fin 11))
  have hf : Nonempty (Derivation body Theta A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have ihj := renameInto ih (Sum.inl : alpha → alpha ⊕ Fin 11) Theta (by
    intro q hq
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩))
  simp only [InductionSyntaxProof.belowFuelRename,sucRelabel] at ihj
  exact Classical.choice (PositiveProof.atKnown n (v 0) (v 1) (v 6) f (v 7) (v 8) (v 9) (v 10) (v 2) (v 3) (v 4) (v 5)
    ihj (andLeft (andLeft (andLeft (andLeft hf)))) (andRight (andLeft (andLeft (andLeft hf))))
    (andRight (andLeft (andLeft hf))) (andRight (andLeft hf)) (andRight hf))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.PositiveInductionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.PositiveInductionProof
