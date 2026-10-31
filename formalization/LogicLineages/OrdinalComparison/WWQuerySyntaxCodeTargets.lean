module
public import LogicLineages.OrdinalComparison.WWQuerySyntaxCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets
open ForwardTranslation

def VectorSyntaxNormalizationCorrect : Prop :=
  ∀ (ι : Type) (n : Nat) (index : ι → Nat) (v : CompiledVector ι n),
    normalizeVectorSyntaxCode (v.syntaxCode index) = v.code index

def QuerySyntaxNormalizationCorrect : Prop :=
  ∀ (ι : Type) (n m : Nat) (index : ι → Nat) (strict : Bool)
    (a : CompiledVector ι n) (b : CompiledVector ι m),
    normalizeQuerySyntaxCode (compiledQuerySyntaxCode index strict a b) =
      compiledQueryCode index strict a b

def QuerySyntaxNormalizationPrimitiveRecursive : Prop := Primrec normalizeQuerySyntaxCode

def SyntaxQueryComputable : Prop := Computable (fun p : EncodedQuery × List Nat => syntaxQueryAt p.1 p.2)
end LogicLineages.OrdinalComparison.Source.Targets
