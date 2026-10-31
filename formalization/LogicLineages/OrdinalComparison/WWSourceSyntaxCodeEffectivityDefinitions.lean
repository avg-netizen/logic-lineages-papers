module
public import LogicLineages.OrdinalComparison.WWSourceSyntaxCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SyntaxCode
/-- The actual parser's numerical output in the fixed raw-source codec.
Valid canonical codes are retained; malformed codes are rejected. -/
def parseCode (n : Nat) : Option Nat := (decode n).map code
end LogicLineages.OrdinalComparison.Source.SyntaxCode
