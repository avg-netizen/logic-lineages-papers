module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ConcreteHeadMoveLayer.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadMoveFields.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.StructuralNumberedLayer.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ResultStructuralFields.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansionSoundness.AppendCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ConcreteHeadMoveLayer.SupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (eqn eqnRelabel)
open InternalTagArithmeticSupportProof InternalPositiveUnfoldingSupportProof
open InternalQuotientComparisonProof InternalBetaTotalityProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type}
attribute [local irreducible] programGraph

def Maps (Gamma : List (Formula alpha)) (p q : Formula alpha) : Prop :=
  ∀ Theta : List (Formula alpha), (∀ a ∈ Gamma, a ∈ Theta) →
    Nonempty (Derivation body Theta p) → Nonempty (Derivation body Theta q)
theorem reflexive (Gamma : List (Formula alpha)) (p : Formula alpha) :
    Maps (body := body) Gamma p p := by intro _ _ h; exact h

theorem andMap {Gamma : List (Formula alpha)} {p q r s : Formula alpha}
    (h : Maps (body := body) Gamma p q) (k : Maps (body := body) Gamma r s) :
    Maps (body := body) Gamma (p ⊓ r) (q ⊓ s) := by
  intro Theta hi d
  exact andIntro (h Theta hi (andLeft d)) (k Theta hi (andRight d))

theorem orMap {Gamma : List (Formula alpha)} {p q r s : Formula alpha}
    (h : Maps (body := body) Gamma p q) (k : Maps (body := body) Gamma r s) :
    Maps (body := body) Gamma (p ⊔ r) (q ⊔ s) := by
  intro Theta hi d
  obtain ⟨d⟩ := d
  obtain ⟨hp⟩ := h (p :: Theta) (fun a ha => List.mem_cons_of_mem _ (hi a ha))
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hr⟩ := k (r :: Theta) (fun a ha => List.mem_cons_of_mem _ (hi a ha))
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨disjunctionElimination d (Derivation.implicationIntroduction (orLeft hp))
    (Derivation.implicationIntroduction (orRight hr))⟩

theorem outputMaps {Gamma : List (Formula alpha)} {m : Nat} (p : Program m)
    (out : OTerm alpha) (xs : Fin m → OTerm alpha)
    (hp : Nonempty (Derivation body Gamma (programGraph p out xs))) :
    Maps (body := body) Gamma (eqn out (numeral 1)) (programGraph p (numeral 1) xs) ∧
    Maps (body := body) Gamma (programGraph p (numeral 1) xs) (eqn out (numeral 1)) := by
  have weaken (Theta : List (Formula alpha)) (hi : ∀ a ∈ Gamma, a ∈ Theta) :
      Nonempty (Derivation body Theta (programGraph p out xs)) := by
    obtain ⟨d⟩ := hp
    exact ⟨Derivation.weakening hi d⟩
  constructor
  · intro Theta hi he
    exact outputTransport p out (numeral 1) xs he (weaken Theta hi)
  · intro Theta hi hq
    have he := functionalApply (OrdinaryArithmetic.graphFormula p)
      (InternalRecursionClosureProof.actualOriginalPrograms body m p).2 Theta out (numeral 1) xs
      (weaken Theta hi) hq
    simpa only [InternalSourceInversionSupportProof.onEquality] using he
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ConcreteHeadMoveLayer.SupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ConcreteHeadMoveLayer.SupportProof
