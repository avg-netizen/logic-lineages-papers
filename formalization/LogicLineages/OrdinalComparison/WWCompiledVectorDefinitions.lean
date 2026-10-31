module
public import LogicLineages.OrdinalComparison.WWEncodedScalarDefinitions
public import LogicLineages.OrdinalComparison.WWAdmissibleAssignmentDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ForwardTranslation

structure CompiledVector (ι : Type) (n : Nat) where
  scalar : Scalar ι
  positive : Fin n → ClosedPositive

noncomputable def CompiledVector.value {ι : Type} {n : Nat}
    (v : CompiledVector ι n) (ρ : ι → Nat) : Fin (n+1) → Ordinal :=
  Fin.cases (v.scalar.value ρ : Ordinal) (fun j => (v.positive j).evaluate.1.repr)

/-- Exact finite compiler, keeping the scalar and every positive field. No
coordinates are dropped by their values, and no positive field is supplied
by a semantic oracle. -/
def compileVector {Γ : List Ty} {n : Nat} (v : OrdinalVector Γ n) :
    Option (CompiledVector (OrdinalComponent Γ) n) := do
  let s ← compileScalar (v 0)
  let p ← AdmissibleAssignment.collect n (fun j => extractPositive (v j.succ))
  pure ⟨s, p⟩

/-- Concrete normal-note codes for every positive field, in coordinate order. -/
def CompiledVector.positiveCodes {ι : Type} {n : Nat} (v : CompiledVector ι n) : List Nat :=
  List.ofFn (fun j => rawNoteEncode (v.positive j).evaluate.1)
end LogicLineages.OrdinalComparison.Source.ForwardTranslation
