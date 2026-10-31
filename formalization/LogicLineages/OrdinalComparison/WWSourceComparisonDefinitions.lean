module
public import LogicLineages.OrdinalComparison.WWCompiledVectorDefinitions
public import LogicLineages.OrdinalComparison.WWEncodedComparisonDefinitions
public import LogicLineages.OrdinalComparison.SourceTypedPortsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ForwardTranslation
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

def CompiledVector.positiveNotes {ι : Type} {n : Nat} (v : CompiledVector ι n) : List NONote :=
  List.ofFn (fun j => (v.positive j).evaluate)

def CompiledVector.code {ι : Type} {n : Nat} (index : ι → Nat) (v : CompiledVector ι n) : EncodedVector :=
  (scalarCode index v.scalar, normalCodes v.positiveNotes)

def compiledQueryCode {ι : Type} {n m : Nat} (index : ι → Nat) (strict : Bool)
    (a : CompiledVector ι n) (b : CompiledVector ι m) : EncodedQuery :=
  (strict, a.code index, b.code index)

/-- Original zero padding outside the actual vector, with ordinal rather
than encoded numerical comparison as its independent semantics. -/
noncomputable def sourceVectorAtValue {Γ : List Ty} {n : Nat}
    (v : OrdinalVector Γ n) (ρ : OrdinalComponent Γ → Nat) (j : Nat) : Ordinal :=
  denote (fun x => (ρ x : Ordinal)) (ordinalVectorAt v j)

noncomputable def SourceComparisonAt {Γ : List Ty} {n m : Nat} (strict : Bool)
    (a : OrdinalVector Γ n) (b : OrdinalVector Γ m) (ρ : OrdinalComponent Γ → Nat) : Prop :=
  (∀ j : Nat, sourceVectorAtValue a ρ (j+1) ≤ sourceVectorAtValue b ρ (j+1)) ∧
    (if strict then sourceVectorAtValue a ρ 0 < sourceVectorAtValue b ρ 0
     else sourceVectorAtValue a ρ 0 ≤ sourceVectorAtValue b ρ 0)

/-- Executable actual source compiler. The same policy and context-position
map is used on both sides; free names are not independently copied. -/
def compileSourceQuery {Γ : List Ty} {τ υ : Ty} (p : AdmissibleSum.Policy)
    (strict : Bool) (a : OriginalTerm Γ τ) (b : OriginalTerm Γ υ) : Option EncodedQuery := do
  let av ← AdmissibleAssignment.assignment p a
  let bv ← AdmissibleAssignment.assignment p b
  let ac ← compileVector av
  let bc ← compileVector bv
  pure (compiledQueryCode (fun c => SourceTypedPorts.variableIndex c.2.1) strict ac bc)
end LogicLineages.OrdinalComparison.Source.ForwardTranslation
