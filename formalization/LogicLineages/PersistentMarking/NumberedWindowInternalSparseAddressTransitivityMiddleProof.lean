module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressTransitivityTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceInversionSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressTransitivityMiddleProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm graph)
open ID1Completion.InternalGraphCompositionEqualityProof (graphInputTransport)
open ID1Completion.InternalControlGraphSupportProof (valueUnique)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn emb)
open ID1Completion.InternalSourceInversionSupportProof (onEquality)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalFreshProbeParsedEmitter (rawContext rawResult rawLeast)
open NumberedWindowInternalSparseAddressPositiveOpenTargets (addressReport)
open NumberedWindowInternalSparsePositiveHeadDecompositionTargets (positiveAt)
open NumberedWindowInternalSparsePositiveOutputTargets (args5)
open NumberedWindowInternalSparsePositiveFold (positive)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem joinMiddle (mid c₁ t₁ k₁ c₂ t₂ k₂ : OTerm α)
    (a : Nonempty (Derivation body Γ (addressReport mid c₁ t₁ k₁)))
    (b : Nonempty (Derivation body Γ (addressReport mid c₂ t₂ k₂))) :
    Nonempty (Derivation body Γ (eqn c₂ c₁)) ∧
    Nonempty (Derivation body Γ (eqn t₂ t₁)) ∧
    Nonempty (Derivation body Γ (eqn k₂ k₁)) := by
  obtain ⟨a⟩ := a
  obtain ⟨b⟩ := b
  let xs : Fin 1 → OTerm α := ![mid]
  have a' := Derivation.conjunctionRight a
  have b' := Derivation.conjunctionRight b
  have a'' := Derivation.conjunctionRight a'
  have b'' := Derivation.conjunctionRight b'
  exact ⟨valueUnique rawContext c₂ c₁ xs ⟨Derivation.conjunctionLeft b'⟩ ⟨Derivation.conjunctionLeft a'⟩,
    valueUnique rawResult t₂ t₁ xs ⟨Derivation.conjunctionLeft b''⟩ ⟨Derivation.conjunctionLeft a''⟩,
    valueUnique rawLeast k₂ k₁ xs ⟨Derivation.conjunctionRight b''⟩ ⟨Derivation.conjunctionRight a''⟩⟩

attribute [local irreducible] programGraph positive

theorem movePositive (raw : Program 5) (least : Program 3) (c₁ t₁ k₁ c₂ t₂ k₂ cert dest : OTerm α)
    (hc : Nonempty (Derivation body Γ (eqn c₂ c₁)))
    (ht : Nonempty (Derivation body Γ (eqn t₂ t₁)))
    (hk : Nonempty (Derivation body Γ (eqn k₂ k₁)))
    (known : Nonempty (Derivation body Γ (positiveAt raw least c₂ t₂ k₂ cert dest))) :
    Nonempty (Derivation body Γ (positiveAt raw least c₁ t₁ k₁ cert dest)) := by
  let xs := args5 c₂ t₂ k₂ cert dest
  let ys := args5 c₁ t₁ k₁ cert dest
  have eqAt : ∀ k, Nonempty (Derivation body Γ (eqn (xs k) (ys k))) := by
    intro k
    exact Fin.cases hc (Fin.cases ht (Fin.cases hk
      (Fin.cases ⟨Derivation.equalityReflexivity (emb cert)⟩
        (Fin.cases ⟨Derivation.equalityReflexivity (emb dest)⟩ (fun e => Fin.elim0 e))))) k
  -- The accepted chart is still the same original Program5 graph.
  -- Expose only its graph constructor, never the selected fold AST.
  unfold positiveAt at known ⊢
  unfold programGraph at known ⊢
  apply graphInputTransport body α 5 Γ (OrdinaryArithmetic.graphFormula (positive raw least))
    (suc z) xs ys _ known
  intro k
  rw [onEquality]
  exact eqAt k

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressTransitivityMiddleProof
