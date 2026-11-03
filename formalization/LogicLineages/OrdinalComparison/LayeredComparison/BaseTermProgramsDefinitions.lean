module
public import LogicLineages.OrdinalComparison.LayeredComparison.CommonLayerSyntaxDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BaseTermPrograms
open CommonLayerSyntax
abbrev Table:=List Nat
abbrev Input:=Nat×Table
abbrev Result:=Nat×List Nat

def valuation (table:Table) (i:Nat):Nat:=table.getD i 1
def valueCode (code:Nat) (table:Table):Nat:=(BaseTerm.decode code).value (valuation table)
def variablesCode (code:Nat):List Nat:=(BaseTerm.decode code).variables

def children (p:Input):List Input:=
  if p.1%4=2 then [((p.1/4).unpair.1,p.2),((p.1/4).unpair.2,p.2)]
  else if p.1%4=3 then [(p.1/4,p.2)] else []

def assemble (p:Input) (results:List Result):Result:=
  if p.1%4=0 then (p.1/4,[])
  else if p.1%4=1 then (valuation p.2 (p.1/4),[p.1/4])
  else if p.1%4=2 then ((results.getD 0 (0,[])).1+(results.getD 1 (0,[])).1,
    (results.getD 0 (0,[])).2++(results.getD 1 (0,[])).2)
  else (Phi (results.getD 0 (0,[])).1,(results.getD 0 (0,[])).2)

def joint (p:Input):Result:=(valueCode p.1 p.2,variablesCode p.1)
end LogicLineages.OrdinalComparison.LayeredComparison.BaseTermPrograms
