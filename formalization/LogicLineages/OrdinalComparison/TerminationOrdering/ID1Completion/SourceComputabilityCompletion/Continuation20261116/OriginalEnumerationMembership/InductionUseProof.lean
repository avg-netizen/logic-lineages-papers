module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.InductionBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCoprimeMultipleBoundedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.InductionUseProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open Continuation20261115 Induction
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem predecessor (n : Nat) (fuel node param p2 p3 out raw bound types heads labels tupleBound : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowFuel n (suc fuel))))
    (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node bound fuel)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing param types p2)))
    (h2 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing p2 heads p3)))
    (h3 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing p3 labels tupleBound)))
    (he : Nonempty (Derivation body Delta (graph2 (OriginalEnumerationRecursion.enumeration n) out node param))) :
    (Nonempty (Derivation body Delta (graph2 contains (numeral 1) out raw)) ↔
     Nonempty (Derivation body Delta (Meaning.holds n raw bound fuel types heads labels tupleBound))) := by
  have hc := InductionBindingProof.belowFuelAt n (suc fuel) fuel hi (InternalCoprimeMultipleBoundedProof.selfLtSucc fuel)
  have hb := InductionBindingProof.atFuelApply n fuel node param p2 p3 out raw bound types heads labels tupleBound hc
    (andIntro (andIntro (andIntro (andIntro hn hp) h2) h3) he)
  constructor
  · intro hm
    exact ⟨Derivation.implicationElimination (Classical.choice (andLeft hb)) (Classical.choice hm)⟩
  · intro hm
    exact ⟨Derivation.implicationElimination (Classical.choice (andRight hb)) (Classical.choice hm)⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.InductionUseProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.InductionUseProof
