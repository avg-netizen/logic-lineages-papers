module
public import LogicLineages.OrdinalComparison.WWSourceSyntaxCodeCheckDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SyntaxCode.Targets

def CheckCodeExact : Prop := ∀ Γ r, check Γ (code r) = inferRaw Γ r

def CheckParserExact : Prop := ∀ Γ n, check Γ n = (decode n).bind (inferRaw Γ)

def TypedRawExact : Prop := ∀ (Γ : List Ty) (τ : Ty) r,
  inferRaw (Γ.map typeCode) r = some (typeCode τ) ↔ ∃ t : OriginalTerm Γ τ, erase t = r

def TypedCheckExact : Prop := ∀ (Γ : List Ty) (τ : Ty) n,
  check (Γ.map typeCode) n = some (typeCode τ) ↔ ∃ t : OriginalTerm Γ τ, encodeTerm t = n

def CheckPrimitiveRecursive : Prop := Primrec (fun p : List Nat × Nat => check p.1 p.2)
end LogicLineages.OrdinalComparison.Source.SyntaxCode.Targets
