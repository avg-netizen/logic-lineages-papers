module
public import LogicLineages.OrdinalComparison.WWSourceSyntaxQueryDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets
open ForwardTranslation

def SourceSyntaxQueryNormalization : Prop :=
  ∀ (Γ : List Ty) (τ υ : Ty) (p : AdmissibleSum.Policy) (strict : Bool)
    (a : OriginalTerm Γ τ) (b : OriginalTerm Γ υ),
    (compileSourceSyntaxQuery p strict a b).map normalizeQuerySyntaxCode =
      compileSourceQuery p strict a b

def SourceSyntaxCodeNormalization : Prop :=
  ∀ (Γ : List Ty) (τ υ : Ty) (p : AdmissibleSum.Policy) (strict : Bool)
    (a : OriginalTerm Γ τ) (b : OriginalTerm Γ υ),
    (compileSourceSyntaxCode p strict a b).map normalizeAritySyntaxCode =
      compileSourceCode p strict a b

def AritySyntaxNormalizationPrimitiveRecursive : Prop := Primrec normalizeAritySyntaxCode
end LogicLineages.OrdinalComparison.Source.Targets
