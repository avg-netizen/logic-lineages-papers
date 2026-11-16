module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.InductionBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.ZeroProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.ZeroInductionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z zRelabel)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open Continuation20261115 Induction
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem atZero (n : Nat) : Nonempty (Derivation body Delta (AtFuel n (z : OTerm alpha))) := by
  apply InductionBindingProof.atFuelIntro
  unfold matrix
  simp only [zRelabel]
  apply Nonempty.intro
  apply Derivation.implicationIntroduction
  let v (i : Fin 11) : OTerm (alpha ⊕ Fin 11) := .var (.inr i)
  let A : Formula (alpha ⊕ Fin 11) :=
    graph2 InternalPairing.pairing (v 0) (v 6) z ⊓
      graph2 InternalPairing.pairing (v 1) (v 7) (v 2) ⊓
      graph2 InternalPairing.pairing (v 2) (v 8) (v 3) ⊓
      graph2 InternalPairing.pairing (v 3) (v 9) (v 10) ⊓
      graph2 (OriginalEnumerationRecursion.enumeration n) (v 4) (v 0) (v 1)
  have hf : Nonempty (Derivation body (A :: Delta.map (fun q => q.relabel Sum.inl)) A) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact Classical.choice (ZeroProof.atKnownFormula n (v 0) (v 1) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9) (v 10)
    (andLeft (andLeft (andLeft (andLeft hf)))) (andRight hf))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.ZeroInductionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.ZeroInductionProof
