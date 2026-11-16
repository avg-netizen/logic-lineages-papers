module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.InductionWitnessProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.InductionBindingProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open SourceComputabilityFormulaSupportProof InternalTagArithmeticSyntaxProof
open InternalStrongInduction InternalStrongInductionProof InternalStrongInductionSyntaxProof
open Induction InductionSyntaxProof
open Continuation20261115
open InternalApplicationStepPeelSupportProof (andIntro)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem atFuelIntro (n : Nat) (raw : OTerm alpha)
    (h : Nonempty (Derivation body (Delta.map (fun q => q.relabel Sum.inl)) (matrix n raw))) :
    Nonempty (Derivation body Delta (AtFuel n raw)) :=
  InternalClosedProgramsBindingProof.introduction body alpha 11 Delta _ h

theorem atFuelApply (n : Nat) (fuel node param p2 p3 out raw bound types heads labels tupleBound : OTerm alpha)
    (h : Nonempty (Derivation body Delta (AtFuel n fuel)))
    (hf : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node bound fuel ⊓
      graph2 InternalPairing.pairing param types p2 ⊓
      graph2 InternalPairing.pairing p2 heads p3 ⊓
      graph2 InternalPairing.pairing p3 labels tupleBound ⊓
      graph2 (OriginalEnumerationRecursion.enumeration n) out node param))) :
    Nonempty (Derivation body Delta ((graph2 contains (numeral 1) out raw).imp (Meaning.holds n raw bound fuel types heads labels tupleBound) ⊓ (Meaning.holds n raw bound fuel types heads labels tupleBound).imp (graph2 contains (numeral 1) out raw))) := by
  obtain ⟨h⟩ := InternalClosedProgramsBindingProof.elimination body alpha 11 Delta
    (matrix n fuel) (fun i => emb ((![node,param,p2,p3,out,raw,bound,types,heads,labels,tupleBound] : Fin 11 → OTerm alpha) i)) h
  rw [InductionWitnessProof.matrixWitness] at h
  obtain ⟨hf⟩ := hf
  exact ⟨Derivation.implicationElimination h hf⟩

theorem belowFuelAt (n : Nat) (raw child : OTerm alpha)
    (h : Nonempty (Derivation body Delta (BelowFuel n raw)))
    (hl : Nonempty (Derivation body Delta (InternalLessThan.strictLess child raw))) :
    Nonempty (Derivation body Delta (AtFuel n child)) := by
  obtain ⟨h⟩ := h
  obtain ⟨hl⟩ := hl
  have d := Derivation.universalElimination (emb child) h
  change Derivation body Delta (instantiate
    ((InternalOriginalOrderSyntaxProof.ltF (.var (.inr 0)) (raw.relabel Sum.inl)).imp
      (predicate n)) (emb child)) at d
  rw [belowElimSyntax,predicateInstantiate] at d
  exact ⟨Derivation.implicationElimination d hl⟩

/-- The smaller-input hypothesis and its universal parameters are discharged
inside the original strong-induction derivation. -/
theorem fuelInduction (n : Nat) (raw : OTerm alpha)
    (step : ∀ (beta : Type) (Theta : List (Formula beta)) (r : OTerm beta),
      Nonempty (Derivation body Theta (BelowFuel n r)) →
      Nonempty (Derivation body Theta (AtFuel n r))) :
    Nonempty (Derivation body Delta (AtFuel n raw)) := by
  let theta : Formula (alpha ⊕ Fin 1) := predicate n
  have hs : Nonempty (Derivation body
      (InternalStrongInduction.below (lift theta) (.var (.inr 0)) :: Delta.map weaken) theta) := by
    change Nonempty (Derivation body
      (InternalStrongInduction.below (lift (predicate n)) (.var (.inr 0)) :: Delta.map weaken)
      (AtFuel n (.var (.inr 0))))
    rw [predicateLift]
    exact step (alpha ⊕ Fin 1) _ (.var (.inr 0)) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨d⟩ := strongInduction theta hs
  have e := Derivation.universalElimination (emb raw) d
  change Derivation body Delta (instantiate (predicate n) (emb raw)) at e
  rw [predicateInstantiate] at e
  exact ⟨e⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.InductionBindingProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.InductionBindingProof
