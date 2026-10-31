module
public import LogicLineages.OrdinalComparison.WWSourceSyntaxCodeTypesDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SyntaxCode.Targets

def TypeDecodeEncode : Prop := ∀ τ, decodeType (typeCode τ) = τ
def TypeEncodeDecode : Prop := ∀ n, typeCode (decodeType n) = n
def TypeLevelExact : Prop := ∀ τ, typeLevel (typeCode τ) = τ.level
def TypeLevelPrimitiveRecursive : Prop := Primrec typeLevel
def TypeConstructorsPrimitiveRecursive : Prop :=
  Primrec₂ arrowCode ∧ Primrec caseCode ∧ Primrec recCode
end LogicLineages.OrdinalComparison.Source.SyntaxCode.Targets
