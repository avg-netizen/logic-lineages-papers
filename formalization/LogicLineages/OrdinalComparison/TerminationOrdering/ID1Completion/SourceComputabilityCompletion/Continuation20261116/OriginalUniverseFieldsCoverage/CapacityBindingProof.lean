module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.CapacitySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.InductionBindingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.CapacityBindingProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalTagArithmeticSyntaxProof hiding OTerm
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalRawListRecursionSyntaxProof (consTermSubst emptySubst)
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalAdditionLawsProof InternalOriginalOrderSyntaxProof InternalOriginalOrderProof
open InternalQuotientComparisonSyntaxProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Induction
variable {alpha : Type}
attribute [local irreducible] programGraph
open ScalarSyntaxProof CapacitySyntaxProof
variable {body : Positive (Fin 1)} {Delta : List (Formula alpha)}

theorem witness (n : Nat) (raw : OTerm alpha) (xs : Fin 11 → OTerm alpha) (labels bound : OTerm alpha) :
    (capacityBody n raw xs).subst (Sum.elim Term.var (fun i => emb (![labels,bound] i))) =
      (InternalLessThan.strictLess (xs 9) (suc bound) ⊓ InternalLessThan.strictLess (xs 10) (suc labels)).imp
        (OriginalEnumerationFields.Targets.accepted n raw (xs 7) (xs 3) (xs 4) labels bound) := by
  have he : Sum.elim Term.var (fun i => emb (![labels,bound] i)) =
      (fun a => emb (Sum.elim Term.var ![labels,bound] a)) := by
    funext a; cases a <;> rfl
  unfold capacityBody
  rw [he]
  simp only [impSubst,conjunctionSubst,InternalLessThan.strictLess,orderSubst,sucSubst,fieldsSubst,
    witnessLift,Term.subst,Sum.elim_inr,Matrix.cons_val_zero,Matrix.cons_val_one]

theorem introduce (n : Nat) (raw : OTerm alpha) (xs : Fin 11 → OTerm alpha)
    (h : Nonempty (Derivation body (Delta.map (fun q => q.relabel Sum.inl)) (capacityBody n raw xs))) :
    Nonempty (Derivation body Delta (capacity n raw xs)) :=
  InternalClosedProgramsBindingProof.introduction body alpha 2 Delta (capacityBody n raw xs) h

theorem applyBound (n : Nat) (raw : OTerm alpha) (xs : Fin 11 → OTerm alpha) (labels bound : OTerm alpha)
    (h : Nonempty (Derivation body Delta (capacity n raw xs)))
    (hs : Nonempty (Derivation body Delta (InternalLessThan.strictLess (xs 9) (suc bound))))
    (hl : Nonempty (Derivation body Delta (InternalLessThan.strictLess (xs 10) (suc labels)))) :
    Nonempty (Derivation body Delta (OriginalEnumerationFields.Targets.accepted n raw (xs 7) (xs 3) (xs 4) labels bound)) := by
  obtain ⟨hi⟩ := InternalClosedProgramsBindingProof.elimination body alpha 2 Delta
    (capacityBody n raw xs) (fun i => emb (![labels,bound] i)) h
  rw [witness] at hi
  exact ⟨Derivation.implicationElimination hi
    (Derivation.conjunctionIntroduction (Classical.choice hs) (Classical.choice hl))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.CapacityBindingProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.CapacityBindingProof
