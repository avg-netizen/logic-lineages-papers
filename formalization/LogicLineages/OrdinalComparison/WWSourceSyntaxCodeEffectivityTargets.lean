module
public import LogicLineages.OrdinalComparison.WWSourceSyntaxCodeEffectivityDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SyntaxCode.Targets

def ParserExact : Prop := ∀ n m, parseCode n = some m ↔ m=n ∧ ∃ r, decode n = some r
def ParserPrimitiveRecursive : Prop := Primrec parseCode
end LogicLineages.OrdinalComparison.Source.SyntaxCode.Targets
