module
public import LogicLineages.OrdinalComparison.WWSourceComparisonDefinitions
public import LogicLineages.OrdinalComparison.WWEncodedCounterBoundDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ForwardTranslation

def compileSourceCode {Γ : List Ty} {τ υ : Ty} (p : AdmissibleSum.Policy)
    (strict : Bool) (a : OriginalTerm Γ τ) (b : OriginalTerm Γ υ) : Option Nat :=
  (compileSourceQuery p strict a b).map (fun q => Encodable.encode (Γ.length, q))
end LogicLineages.OrdinalComparison.Source.ForwardTranslation
