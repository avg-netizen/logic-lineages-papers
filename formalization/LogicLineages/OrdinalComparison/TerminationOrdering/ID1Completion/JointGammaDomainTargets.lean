module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaDomainDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaDomainTargets
open Source JointGammaDomain
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- About this exact concrete codec, not arbitrary Encodable instances. -/
def ActualObjectCodec : Prop :=
  (∀ code : Nat, ∃ obj : ContextUniform.Object, Encodable.decode code = some obj) ∧
  (∀ (code : Nat) (obj : ContextUniform.Object),
    Encodable.decode code = some obj ↔ ContextUniform.objectCode obj.1 obj.2 = code) ∧
  (∀ code : Nat, Encodable.decode₂ ContextUniform.Object code = Encodable.decode code)

def ActualGuardPrimitive : Prop := Primrec guardValue

def ActualGuardCalibration : Prop :=
  (∀ f a : Nat, guardValue (List.Vector.ofFn ![f,a]) = 1 ↔ sameContext f a) ∧
  (∀ (Gamma Delta : List Ty) (x y : Nat),
    sameContext (ContextUniform.objectCode Gamma x) (ContextUniform.objectCode Delta y) ↔ Gamma = Delta)

/-- Exactly the original Gamma fiber; no foreign argument is included. -/
def ActualArgumentDomain : Prop :=
  ∀ (Gamma : List Ty) (x u : Nat),
  sameContext (ContextUniform.objectCode Gamma x) u ↔
    ∃ a : Nat, u = ContextUniform.objectCode Gamma a

def ActualQuantifierFibers : Prop :=
  ∀ (Gamma : List Ty) (x : Nat) (Q : Nat → Prop),
  ((∀ u, sameContext (ContextUniform.objectCode Gamma x) u → Q u) ↔
    ∀ a, Q (ContextUniform.objectCode Gamma a)) ∧
  ((∃ u, sameContext (ContextUniform.objectCode Gamma x) u ∧ Q u) ↔
    ∃ a, Q (ContextUniform.objectCode Gamma a))

def ActualTypedArgumentFibers : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (context typ x : Nat) (Q : Nat → Prop),
  (∀ u, sameContext (ContextUniform.objectCode Gamma x) u →
    JointGammaTyped.encodedTyped n arity context typ u → Q u) ↔
  ∀ a, OrdinaryArithmeticTypedCarrier.encodedTyped n arity Gamma context typ a →
    Q (ContextUniform.objectCode Gamma a)

/-- The ORIGINAL arithmetic graph compiler applied to an actual Program 2. -/
def ActualGuardArithmeticFormula : Prop :=
  ∃ p : Program 2, (∀ v, evaluate p v = guardValue v) ∧
  ∀ f a : Nat, (SourcePresentation.checkerFormula p).Realize ![f,a] ↔ sameContext f a

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaDomainTargets
