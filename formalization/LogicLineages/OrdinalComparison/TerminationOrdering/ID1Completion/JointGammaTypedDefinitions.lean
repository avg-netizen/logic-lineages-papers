module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ContextUniformPrimaryDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaTyped
open Source NumberedUniformPackedDecoding
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

abbrev Input (n : Nat) := (ContextUniformPrimary.Window n × List Ty) × Ty × Nat

/-- Raw-code presentation of the ORIGINAL typed canonical-carrier checker. -/
def rawTypedCarrier (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (tau : Ty) (value : Nat) : Bool :=
  (rawUniverseDecode n arity symbols S Gamma value).any (fun q =>
    decide (q.1 = tau ∧ ContextUniformPrimary.representative arity symbols S Gamma q = value))

/-- Transparent object-code wrapper around the original fixed-context checker.
The existing ContextUniform.Object and all component codes are unchanged. -/
def typedValue (n : Nat) (arity : Fin n → Nat) (v : List.Vector Nat 3) : Nat :=
  match Encodable.decode (α := ContextUniform.Object) (v.get 2) with
  | none => 0
  | some obj => OrdinaryArithmeticTypedCarrier.typedValue n arity obj.1
      (List.Vector.ofFn ![v.get 0,v.get 1,obj.2])

def encodedTyped (n : Nat) (arity : Fin n → Nat) (context typ object : Nat) : Prop :=
  ∃ (Gamma : List Ty) (value : Nat),
    Encodable.decode (α := ContextUniform.Object) object = some (Gamma,value) ∧
    OrdinaryArithmeticTypedCarrier.encodedTyped n arity Gamma context typ value

/-- The unchanged ordinary-arithmetic graph compiler applied to output one. -/
def typedFormula (p : Program 3) : OrdinaryArithmetic.Formula (Fin 3) :=
  OrdinaryArithmetic.applyGraph (OrdinaryArithmetic.graphFormula p)
    (OrdinaryArithmetic.succTerm OrdinaryArithmetic.zeroTerm) ![.var 0,.var 1,.var 2]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaTyped
