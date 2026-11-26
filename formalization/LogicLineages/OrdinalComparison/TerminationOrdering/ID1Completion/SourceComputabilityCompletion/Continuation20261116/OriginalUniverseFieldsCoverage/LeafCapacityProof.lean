module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.InductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.CapacityBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ResultSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ObservationPartsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.VariableProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.BottomProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.LeafCapacityProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open Induction
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)


/-- Discharges the two capacity binders; the callback is used only for the
capacity-independent leaf cases and is proved below from actual observations. -/
theorem introduceUnconditional (n : Nat) (raw : OTerm alpha) (xs : Fin 11 → OTerm alpha)
    (h : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)),
      (∀ q ∈ Delta, q.relabel j ∈ Theta) → ∀ (labels bound : OTerm beta),
      Nonempty (Derivation body Theta (OriginalEnumerationFields.Targets.accepted n
        (raw.relabel j) ((xs 7).relabel j) ((xs 3).relabel j) ((xs 4).relabel j) labels bound))) :
    Nonempty (Derivation body Delta (capacity n raw xs)) := by
  apply CapacityBindingProof.introduce
  let premise : Formula (alpha ⊕ Fin 2) :=
    InternalLessThan.strictLess ((xs 9).relabel Sum.inl) (suc (.var (.inr 1))) ⊓
    InternalLessThan.strictLess ((xs 10).relabel Sum.inl) (suc (.var (.inr 0)))
  obtain ⟨d⟩ := h (alpha ⊕ Fin 2) Sum.inl
    (premise :: Delta.map (fun q => q.relabel Sum.inl))
    (fun q hq => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩)) (.var (.inr 0)) (.var (.inr 1))
  exact ⟨Derivation.implicationIntroduction d⟩

theorem variableCode (n : Nat) (arity : Fin n → Nat) (H : Program 1)
    (raw field : OTerm alpha) (xs : Fin 11 → OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableConstructor raw field)))
    (ho : Nonempty (Derivation body Delta (observations n arity H false raw xs))) :
    Nonempty (Derivation body Delta (capacity n raw xs)) := by
  apply introduceUnconditional n raw xs
  intro beta j Theta hj labels bound
  have hcj := renameInto hc j Theta hj
  rw [graph1Rename] at hcj
  have hoj := renameInto ho j Theta hj
  rw [ResultSyntaxProof.observationsRename] at hoj
  exact VariableProof.atConstructor n arity H (raw.relabel j) (field.relabel j)
    ((xs 5).relabel j) ((xs 6).relabel j) ((xs 2).relabel j) ((xs 7).relabel j)
    ((xs 3).relabel j) ((xs 4).relabel j) labels bound hcj
    (ObservationPartsProof.admission _ _ _ false _ _ hoj)
    (ObservationPartsProof.length _ _ _ false _ _ hoj)

theorem bottom (n : Nat) (arity : Fin n → Nat) (H : Program 1)
    (raw field : OTerm alpha) (xs : Fin 11 → OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.bottomConstructor raw field)))
    (ho : Nonempty (Derivation body Delta (observations n arity H false raw xs))) :
    Nonempty (Derivation body Delta (capacity n raw xs)) := by
  apply introduceUnconditional n raw xs
  intro beta j Theta hj labels bound
  have hcj := renameInto hc j Theta hj
  rw [graph1Rename] at hcj
  have hoj := renameInto ho j Theta hj
  rw [ResultSyntaxProof.observationsRename] at hoj
  exact BottomProof.atConstructor n arity H ((xs 0).relabel j) ((xs 1).relabel j)
    (raw.relabel j) (field.relabel j) ((xs 5).relabel j) ((xs 6).relabel j) ((xs 2).relabel j)
    ((xs 7).relabel j) ((xs 3).relabel j) ((xs 4).relabel j) labels bound hcj
    (ObservationPartsProof.admission _ _ _ false _ _ hoj)
    (ObservationPartsProof.context _ _ _ false _ _ hoj)
    (ObservationPartsProof.types _ _ _ false _ _ hoj)

theorem nilCode (n : Nat) (raw : OTerm alpha) (xs : Fin 11 → OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.nilConstructor raw Fin.elim0))) :
    Nonempty (Derivation body Delta (capacity n raw xs)) := by
  apply introduceUnconditional n raw xs
  intro beta j Theta hj labels bound
  have hcj := renameInto hc j Theta hj
  simp only [programRename,InternalControlGraphSupportProof.emptyRename] at hcj
  exact (OriginalEnumerationFields.LeafProof.internalNil n body beta Theta (raw.relabel j)
    ((xs 7).relabel j) ((xs 3).relabel j) ((xs 4).relabel j) labels bound hcj).mpr
    (OriginalEnumerationValidity.LeafProof.nil n (raw.relabel j) hcj)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.LeafCapacityProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.LeafCapacityProof
