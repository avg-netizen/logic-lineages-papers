module

public import LogicLineages.ComputabilityKnowledge.GorbowPublishedQuantifierTruthDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowPublishedQuantifierTruth.Targets
open GorbowSyntax GorbowPRProgram GorbowTheoryProof GorbowPublishedDCB
open GorbowPublishedModel GorbowRegistryTuple

/-- Every advertised source FUNCTION name, with arbitrary correctly sized numeric arguments.
This asserts only listed named headers, not equality on all raw UF inputs. -/
def NamedFunctions : Prop :=
  ∀ (pF pR : Program 1) (q : Program 5) (c : Code), Actual pF pR q c →
  ∀ name : Nat × Nat, name ∈ GorbowSourceRegistryPadding.functionNames →
  ∀ args : List Nat, args.length = name.1 →
    (ground pF pR q).universalFunction (header name.1 name.2 args) =
      GorbowSourceRegistryPadding.sourceFunction (header name.1 name.2 args)

/-- Every advertised source RELATION name, without a malformed-header assertion. -/
def NamedRelations : Prop :=
  ∀ (pF pR : Program 1) (q : Program 5) (c : Code), Actual pF pR q c →
  ∀ name : Nat × Nat, name ∈ GorbowSourceRegistryPadding.relationNames →
  ∀ args : List Nat, args.length = name.1 →
    ((ground pF pR q).universalRelation (header name.1 name.2 args) ↔
      GorbowSortedRegistry.relationProgram (header name.1 name.2 args) = true)

/-- All finite dispatch equations REQUIRED by the already proved generic quantifier theorem,
now DERIVED for the actual ground; they are not new oracle hypotheses. -/
def SourceDispatch : Prop :=
  ∀ (pF pR : Program 1) (q : Program 5) (c : Code), Actual pF pR q c →
    GorbowRegistryDispatch.RelationLaws (ground pF pR q) ∧
    GorbowRegistryDispatch.FunctionLaws (ground pF pR q)

/-- Literal universally CODED full-closed-L-term forall/ex FS and arithmetic-term UBF.
All supported named variables/formulas are covered, at every actual positive stage. -/
def PositiveQuantifierAxioms : Prop :=
  ∀ (pF pR : Program 1) (q : Program 5) (c : Code), Actual pF pR q c →
  ∀ k : Nat,
    GorbowSortedQuantifierTruth.forallAxiom.realize
      (GorbowPublishedRevision.stage pF pR q c (k+1)) Fin.elim0 ∧
    GorbowSortedQuantifierTruth.existsAxiom.realize
      (GorbowPublishedRevision.stage pF pR q c (k+1)) Fin.elim0 ∧
    GorbowSortedQuantifierTruth.barcanAxiom.realize
      (GorbowPublishedRevision.stage pF pR q c (k+1)) Fin.elim0

def Target : Prop := NamedFunctions ∧ NamedRelations ∧ SourceDispatch ∧ PositiveQuantifierAxioms
end LogicLineages.ComputabilityKnowledge.GorbowPublishedQuantifierTruth.Targets
