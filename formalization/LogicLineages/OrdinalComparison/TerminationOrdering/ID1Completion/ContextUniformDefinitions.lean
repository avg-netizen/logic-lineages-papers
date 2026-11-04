module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourcePresentationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ContextUniform
open Source
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The endpoint payload is unchanged. Its ambient de Bruijn context is now
part of the object code, so lambda bodies in sigma::Gamma and terms in Gamma
are members of ONE inductive predicate. -/
abbrev Object := List Ty × Nat

def objectCode (Gamma : List Ty) (value : Nat) : Nat := Encodable.encode (Gamma,value)

def scalarValue (n : Nat) (arity : Fin n → Nat) (v : List.Vector Nat 2) : Nat :=
  match Encodable.decode (α := Object) (v.get 1) with
  | none => 0
  | some obj => OrdinaryArithmeticCarrier.scalarValue n arity obj.1
      (List.Vector.ofFn ![v.get 0,obj.2])

def listValue (n : Nat) (arity : Fin n → Nat) (v : List.Vector Nat 2) : Nat :=
  match Encodable.decode (α := Object) (v.get 1) with
  | none => 0
  | some obj => OrdinaryArithmeticCarrier.listValue n arity obj.1
      (List.Vector.ofFn ![v.get 0,obj.2])

def positiveValue (n : Nat) (arity : Fin n → Nat) (v : List.Vector Nat 4) : Nat :=
  match Encodable.decode (α := Object) (v.get 1), Encodable.decode (α := Object) (v.get 2) with
  | some source, some target =>
      if source.1 = target.1 then OrdinaryArithmeticQuotient.positiveValue n arity source.1
        (List.Vector.ofFn ![v.get 0,source.2,target.2,v.get 3]) else 0
  | _, _ => 0

def directValue (n : Nat) (arity : Fin n → Nat) (v : List.Vector Nat 4) : Nat :=
  match Encodable.decode (α := Object) (v.get 1), Encodable.decode (α := Object) (v.get 2) with
  | some source, some target =>
      if source.1 = target.1 then OrdinaryArithmeticDirect.directValue n arity source.1
        (List.Vector.ofFn ![v.get 0,source.2,target.2,v.get 3]) else 0
  | _, _ => 0

/-- No semantic/termination premise. These are the exact four checker
equalities which an actual program construction must prove jointly in Gamma. -/
def Calibrated (data : SourcePresentation.Data) (n : Nat) (arity : Fin n → Nat) : Prop :=
  (∀ v, evaluate data.scalar v = scalarValue n arity v) ∧
  (∀ v, evaluate data.multiset v = listValue n arity v) ∧
  (∀ v, evaluate data.positive v = positiveValue n arity v) ∧
  (∀ v, evaluate data.direct v = directValue n arity v)

def encodedScalar (n : Nat) (arity : Fin n → Nat) (context object : Nat) : Prop :=
  ∃ (Gamma : List Ty) (value : Nat), Encodable.decode (α := Object) object = some (Gamma,value) ∧
    OrdinaryArithmeticCarrier.encodedScalar n arity Gamma context value

def encodedList (n : Nat) (arity : Fin n → Nat) (context object : Nat) : Prop :=
  ∃ (Gamma : List Ty) (value : Nat), Encodable.decode (α := Object) object = some (Gamma,value) ∧
    OrdinaryArithmeticCarrier.encodedList n arity Gamma context value

def encodedR (n : Nat) (arity : Fin n → Nat) (context source target : Nat) : Prop :=
  ∃ (Gamma : List Ty) (x y : Nat),
    Encodable.decode (α := Object) source = some (Gamma,x) ∧
    Encodable.decode (α := Object) target = some (Gamma,y) ∧
    PositiveArithmeticOperators.encodedR n arity Gamma context x y

def encodedDirect (n : Nat) (arity : Fin n → Nat) (context source target : Nat) : Prop :=
  ∃ (Gamma : List Ty) (x y : Nat),
    Encodable.decode (α := Object) source = some (Gamma,x) ∧
    Encodable.decode (α := Object) target = some (Gamma,y) ∧
    OrdinaryArithmeticDirect.encodedDirect n arity Gamma context x y

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ContextUniform
