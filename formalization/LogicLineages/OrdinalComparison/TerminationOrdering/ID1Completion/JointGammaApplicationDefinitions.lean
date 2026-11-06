module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ContextUniformPrimaryDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaApplication
open Source NumberedUniformPackedDecoding NumberedAuxiliaryCoding
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

abbrev Input (n : Nat) := (ContextUniformPrimary.Window n × List Ty) × Ty × Ty × Nat × Nat
abbrev DecodedInput := List Ty × Nat × Nat × Nat × Nat × Nat

/-- Raw-code version of the accepted checked applicationProgram. -/
def rawApplication (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (sigma tau : Ty) (x y : Nat) : Option Nat := do
  let f ← rawUniverseDecode n arity symbols S Gamma x
  let a ← rawUniverseDecode n arity symbols S Gamma y
  if f.1 = .arrow sigma tau ∧ a.1 = sigma ∧
      ContextUniformPrimary.representative arity symbols S Gamma f = x ∧
      ContextUniformPrimary.representative arity symbols S Gamma a = y then
    let result ← rawStructuralDecode arity Gamma (tau,Code.app sigma f.2 a.2)
    pure (ContextUniformPrimary.representative arity symbols S Gamma result)
  else none

/-- Three original Object decoders; all objects must share the source Gamma.
No object code is re-encoded or subjected to a new canonical-code test. -/
def applicationValue (n : Nat) (arity : Fin n → Nat) (v : List.Vector Nat 6) : Nat :=
  match Encodable.decode (α := ContextUniform.Object) (v.get 3),
      Encodable.decode (α := ContextUniform.Object) (v.get 4),
      Encodable.decode (α := ContextUniform.Object) (v.get 5) with
  | some f, some a, some z =>
    if f.1 = a.1 ∧ f.1 = z.1 then OrdinaryArithmeticApplication.applicationValue n arity f.1
      (List.Vector.ofFn ![v.get 0,v.get 1,v.get 2,f.2,a.2,z.2]) else 0
  | _, _, _ => 0

def encodedApplication (n : Nat) (arity : Fin n → Nat)
    (context domain codomain f a z : Nat) : Prop :=
  ∃ (Gamma : List Ty) (x y value : Nat),
    Encodable.decode (α := ContextUniform.Object) f = some (Gamma,x) ∧
    Encodable.decode (α := ContextUniform.Object) a = some (Gamma,y) ∧
    Encodable.decode (α := ContextUniform.Object) z = some (Gamma,value) ∧
    OrdinaryArithmeticApplication.decodedApplication n arity Gamma context domain codomain x y = some value

def applicationFormula (p : Program 6) : OrdinaryArithmetic.Formula (Fin 6) :=
  OrdinaryArithmetic.applyGraph (OrdinaryArithmetic.graphFormula p)
    (OrdinaryArithmetic.succTerm OrdinaryArithmetic.zeroTerm) ![.var 0,.var 1,.var 2,.var 3,.var 4,.var 5]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaApplication
