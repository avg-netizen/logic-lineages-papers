module
public import LogicLineages.OrdinalComparison.WWScalarSyntaxCodeDefinitions
public import LogicLineages.OrdinalComparison.WWSourceComparisonDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ForwardTranslation

/-- Literal syntax only: no ordinal normalization is performed by this code. -/
def CompiledVector.syntaxCode {ι : Type} {n : Nat} (index : ι → Nat)
    (v : CompiledVector ι n) : EncodedVector :=
  (scalarSyntaxCode index v.scalar, List.ofFn (fun j => closedPositiveCode (v.positive j)))

def normalizeVectorSyntaxCode (v : EncodedVector) : EncodedVector :=
  (normalizeScalarSyntaxCode v.1, v.2.map encodedClosedPositive)

def compiledQuerySyntaxCode {ι : Type} {n m : Nat} (index : ι → Nat) (strict : Bool)
    (a : CompiledVector ι n) (b : CompiledVector ι m) : EncodedQuery :=
  (strict, a.syntaxCode index, b.syntaxCode index)

def normalizeQuerySyntaxCode (q : EncodedQuery) : EncodedQuery :=
  (q.1, normalizeVectorSyntaxCode q.2.1, normalizeVectorSyntaxCode q.2.2)

noncomputable def syntaxQueryAt (q : EncodedQuery) (xs : List Nat) : Bool :=
  encodedQueryAt (normalizeQuerySyntaxCode q) xs
end LogicLineages.OrdinalComparison.Source.ForwardTranslation
