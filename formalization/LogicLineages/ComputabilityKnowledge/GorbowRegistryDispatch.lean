module

public import LogicLineages.ComputabilityKnowledge.GorbowSortedBooleanTruth
public import LogicLineages.ComputabilityKnowledge.GorbowSortedQuantifierTruth

@[expose] public section
/-! Explicit finite dispatch equations sufficient for the displayed coded
Boolean/quantifier/UBF formulas. They make no assertion about arbitrary other
U/u inputs. An actual concrete registry must separately prove these equations;
this interface is not a representation or source-correctness oracle. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowRegistryDispatch
open GorbowRegistryTuple GorbowSortedRevision

def RelationLaws (g : Ground) : Prop := ∀ a b,
  (g.universalRelation (header 1 0 [a]) ↔ GorbowSortedBooleanCode.sentenceCode a=true) ∧
  (g.universalRelation (header 1 1 [a]) ↔ GorbowSortedBooleanCode.fullTermCode a=true) ∧
  (g.universalRelation (header 1 2 [a]) ↔ GorbowSortedBooleanCode.arithmeticTermCode a=true) ∧
  (g.universalRelation (header 1 3 [a]) ↔ GorbowSortedSyntaxCode.isVariableCode a=true) ∧
  (g.universalRelation (header 2 0 [a,b]) ↔ GorbowSortedNamedCode.namedFormula a b=true)

def FunctionLaws (g : Ground) : Prop := ∀ a b c,
  g.universalFunction (header 1 0 [a])=GorbowSortedBooleanCode.unaryNumber 6 a ∧
  g.universalFunction (header 2 0 [a,b])=GorbowSortedBooleanCode.binaryNumber 7 a b ∧
  g.universalFunction (header 2 1 [a,b])=GorbowSortedBooleanCode.binaryNumber 8 a b ∧
  g.universalFunction (header 2 2 [a,b])=GorbowSortedBooleanCode.binaryNumber 9 a b ∧
  g.universalFunction (header 2 3 [a,b])=(GorbowSortedNamedCode.allNumber a b).getD 0 ∧
  g.universalFunction (header 2 4 [a,b])=(GorbowSortedNamedCode.exNumber a b).getD 0 ∧
  g.universalFunction (header 3 0 [a,b,c])=(GorbowSortedNamedCode.instanceNumber a b c).getD 0
end LogicLineages.ComputabilityKnowledge.GorbowRegistryDispatch
