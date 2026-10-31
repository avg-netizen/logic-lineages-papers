module
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxVectorCompilerDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets
open OrdinalSyntax ForwardTranslation

def OrdinalSyntaxVectorCompilerCorrect : Prop :=
  ∀ (Γ : List Ty) (n : Nat) (v : OrdinalVector Γ n),
    compileVectorCode (vectorCode v) =
      (compileVector v).map (fun c => c.syntaxCode (fun x => SourceTypedPorts.variableIndex x.2.1))

def OrdinalSyntaxVectorCompilerPrimitiveRecursive : Prop := Primrec compileVectorCode
end LogicLineages.OrdinalComparison.Source.Targets
