module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationCoordinateThinGraphProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof
  (compositionValue projectionValue outputTransport valueUnique programRename)
open ID1Completion.InternalAcceptanceSupportProof (programCompositionCases)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

def retained (i : Fin 6) : Prop := i = 1 ∨ i = 2 ∨ i = 3

/-- A local graph transport property, not an indexed proof tree on ASTs.
Only already-present symbolic scratch/context/type terms are compared. -/
def Stable (p : Program 6) : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (out : OTerm α)
    (xs ys : Fin 6 → OTerm α),
      (∀ i, retained i → xs i = ys i) →
      Nonempty (Derivation body Γ (programGraph p out xs)) →
      Nonempty (Derivation body Γ (programGraph p out ys))

theorem stableProjection (i : Fin 6) (hi : retained i) : Stable (.projection i) := by
  intro body α Γ out xs ys same old
  obtain ⟨eq⟩ := valueUnique (.projection i) out (xs i) xs old (projectionValue i xs)
  rw [same i hi] at eq
  exact outputTransport (.projection i) (ys i) out ys ⟨symm eq⟩ (projectionValue i ys)

theorem stableCompose {n : Nat} (f : Program n) (g : Fin n → Program 6)
    (hg : ∀ i, Stable (g i)) : Stable (.composition f g) := by
  intro body α Γ out xs ys same old
  apply programCompositionCases f g out xs (programGraph (.composition f g) out ys) old
  intro β j mids Δ _ outer inner
  rw [programRename]
  apply compositionValue f g (out.relabel j) (fun i => (ys i).relabel j) mids outer
  intro i
  exact hg i body β Δ (mids i) (fun k => (xs k).relabel j) (fun k => (ys k).relabel j)
    (fun k hr => congrArg (fun v => v.relabel j) (same k hr)) (inner i)

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationCoordinateThinGraphProof
