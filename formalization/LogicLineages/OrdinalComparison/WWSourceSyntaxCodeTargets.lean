module
public import LogicLineages.OrdinalComparison.WWSourceSyntaxCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SyntaxCode.Targets

def DecodeEncode : Prop := ∀ r, decode (code r) = some r
def EncodeDecode : Prop := ∀ n r, decode n = some r → code r = n
def CodeInjective : Prop := Function.Injective code
/-- Genuine primitive-recursive numerical constructors of the fixed codec. -/
def ConstructorsPrimitiveRecursive : Prop :=
  Primrec (fun i : Nat => 8*i) ∧ Primrec (fun τ : Nat => 8*τ+3) ∧
  Primrec (fun τ : Nat => 8*τ+4) ∧
  Primrec (fun p : Nat×Nat => 8*Nat.pair p.1 p.2+5) ∧
  Primrec (fun p : Nat×Nat => 8*Nat.pair p.1 p.2+6)
end LogicLineages.OrdinalComparison.Source.SyntaxCode.Targets
