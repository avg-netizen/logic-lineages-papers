module
public import LogicLineages.PermittedControl.GroundComparisonAssemblyTargets
public import LogicLineages.PermittedControl.GroundComparisonPositiveTargets
public import LogicLineages.StandardControlCurrent.PolicyIndexedShapeTargets

@[expose] public section
namespace LogicLineages.PermittedControl.PolicyIndexedGroundDriver
open OrdinalComparison Source Source.AdmissibleSum Source.OrdinalSyntax Source.ForwardTranslation
open GroundComparison (Relation Canonical)
open GroundComparisonReduction (tagOf equalFlag)
open StandardControlCurrent.PolicyIndexedShape (Implements)
open Nat.Partrec (Code)

abbrev TermInput := Nat × Nat × Nat
abbrev IndexedInput := Code × TermInput
abbrev SourceInput := Code × Nat × Nat
abbrev IndexedSource := SourceInput → Part (Option EncodedVector)
abbrev Block := OriginalPrintedRawFamilyFrontend.Args → Option Bool
abbrev Query := Nat → Nat → Nat → OriginalPrintedRawFamilyFrontend.Args

def SourceExact (source : IndexedSource) : Prop :=
  ∀ (e : Code) (p : Policy), Implements e p → ∀ d n : Nat,
    source (e,d,n) = Part.some (StandardControlCurrent.PolicySourceInterface.compile p d n)

/-- The literal positive-coordinate and scalar-query body of
`GroundComparisonAssembly`, independent of any parsing policy. -/
def body (cbd : Block) (query : Query) (rel : Relation) (ea eb : EncodedVector) : Bool :=
  GroundComparisonPositive.positiveTest (equalFlag rel) ea.2 eb.2 &&
    !(decide (cbd (query (tagOf rel) (normalizeScalarSyntaxCode ea.1) (normalizeScalarSyntaxCode eb.1)) =
      some true))

def pointwiseDecision (p : Policy) (cbd : Block) (query : Query) (rel : Relation)
    (x : TermInput) : Bool :=
  ((StandardControlCurrent.PolicySourceInterface.compile p x.1 x.2.1).bind (fun ea =>
    (StandardControlCurrent.PolicySourceInterface.compile p x.1 x.2.2).map
      (fun eb => body cbd query rel ea eb))).getD false

/-- Preserve the original left-to-right refusal, without assigning any
default to an outer computation that diverges. -/
noncomputable def indexedDecision (source : IndexedSource) (cbd : Block) (query : Query)
    (rel : Relation) (x : IndexedInput) : Part Bool :=
  (source (x.1,x.2.1,x.2.2.1)).bind fun
    | none => Part.some false
    | some ea => (source (x.1,x.2.1,x.2.2.2)).map
        (fun ob => (ob.map (fun eb => body cbd query rel ea eb)).getD false)

def ExactIndexedDecision : Prop :=
  ∀ source : IndexedSource, SourceExact source → ∀ (cbd : Block) (query : Query) (rel : Relation)
    (e : Code) (p : Policy), Implements e p → ∀ x : TermInput,
      indexedDecision source cbd query rel (e,x) = Part.some (pointwiseDecision p cbd query rel x)

def IndexedDecisionPartrec : Prop :=
  ∀ source : IndexedSource, Partrec source → ∀ cbd : Block, Computable cbd →
    ∀ query : Query, Computable (fun x : TermInput => query x.1 x.2.1 x.2.2) →
    ∀ rel, Partrec (indexedDecision source cbd query rel)

end LogicLineages.PermittedControl.PolicyIndexedGroundDriver
