module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainParameterDecisionDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceBooleanProgramsDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceParameterDecision
open CommonLayerSyntax

def existsBind (xs : List Nat) (p : SourceFormula) : SourceFormula := xs.foldr SourceFormula.existsNat p
def forallBind (xs : List Nat) (p : SourceFormula) : SourceFormula :=
  xs.foldr (fun i q => .negative (.existsNat i (.negative q))) p

def witnesses (p : SourceFormula) : List Nat :=
  SourceTermGraph.allocated (SourceBooleanGraph.start p) (SourceBooleanGraph.forest p)
def decideExists (xs values : List Nat) (p : SourceFormula) : Option Bool :=
  if SourceBooleanGraph.test p then
    PlainParameterDecision.decideExists (xs ++ witnesses p) values (SourceBooleanGraph.compile p)
  else none
def decideForall (xs values : List Nat) (p : SourceFormula) : Option Bool :=
  (decideExists xs values (.negative p)).map Bool.not

namespace Code
def witnesses (code : Nat) : List Nat := SourceTermGraph.names
  (SourceBooleanPrograms.Code.start code)
  (SourceBooleanPrograms.Code.count (SourceBooleanPrograms.Code.forest code))
def decideExists (xs values : List Nat) (code : Nat) : Option Bool :=
  if SourceBooleanPrograms.Code.test code then
    PlainParameterDecision.Code.decideExists (xs ++ witnesses code) values (SourceBooleanPrograms.Code.compile code)
  else none
def decideForall (xs values : List Nat) (code : Nat) : Option Bool :=
  (decideExists xs values (5 * code + 2)).map Bool.not
end Code

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceParameterDecision
