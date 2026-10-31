module
public import LogicLineages.OrdinalComparison.WWQuerySyntaxCodeDefinitions
public import LogicLineages.OrdinalComparison.WWSourceCodedQueryDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ForwardTranslation

/-- Original assignment and refusing extraction, but output contains literal
scalar/positive AST codes only, without evaluating any ordinal head. -/
def compileSourceSyntaxQuery {Γ : List Ty} {τ υ : Ty} (p : AdmissibleSum.Policy)
    (strict : Bool) (a : OriginalTerm Γ τ) (b : OriginalTerm Γ υ) : Option EncodedQuery := do
  let av ← AdmissibleAssignment.assignment p a
  let bv ← AdmissibleAssignment.assignment p b
  let ac ← compileVector av
  let bc ← compileVector bv
  pure (compiledQuerySyntaxCode (fun c => SourceTypedPorts.variableIndex c.2.1) strict ac bc)

def compileSourceSyntaxCode {Γ : List Ty} {τ υ : Ty} (p : AdmissibleSum.Policy)
    (strict : Bool) (a : OriginalTerm Γ τ) (b : OriginalTerm Γ υ) : Option Nat :=
  (compileSourceSyntaxQuery p strict a b).map (fun q => Encodable.encode (Γ.length, q))

/-- Numeric total normalization, with the already specified malformed-code
fallback of decodeArityQuery. -/
def normalizeAritySyntaxCode (n : Nat) : Nat :=
  Encodable.encode ((decodeArityQuery n).1, normalizeQuerySyntaxCode (decodeArityQuery n).2)
end LogicLineages.OrdinalComparison.Source.ForwardTranslation
