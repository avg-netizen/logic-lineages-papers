module
public import LogicLineages.OrdinalComparison.SourceMachineSpineCodeDefinitions
public import LogicLineages.OrdinalComparison.WWSourceSyntaxCodeCheckDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceMachineQueryCode
abbrev Query := Nat × Nat × Nat
/-- Context length, strict left R, strict right L. Aggregate itself is (L,R). -/
def request (b e : Nat) : Query :=
  (4+(SourceMachineSpineCode.compiled b e).1,
    (SourceMachineSpineCode.aggregate b e).2,(SourceMachineSpineCode.aggregate b e).1)
def pack (q : Query) : Nat := Encodable.encode q
def unpack (n : Nat) : Option Query := Encodable.decode (α:=Query) n
def output (b e : Nat) : Nat := pack (request b e)
end LogicLineages.OrdinalComparison.Source.SourceMachineQueryCode
