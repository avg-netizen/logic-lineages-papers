module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaApplicationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaApplicationTargets
open Source NumberedRewriteSyntax NumberedLeastCodeRepresentative JointGammaApplication
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

def ActualRawApplicationCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (sigma tau : Ty) (x y : Nat),
  rawApplication n arity symbols S Gamma sigma tau x y =
    NumberedNumericApplication.canonicalApplication n arity symbols S Gamma sigma tau x y

def ActualOriginalApplicationPrimitive : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
  Primrec (fun p : Input n => NumberedNumericApplication.canonicalApplication n arity
    p.1.1.1 p.1.1.2 p.1.2 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)

def ActualObjectApplicationPrimitive : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat), Primrec (applicationValue n arity)

def ActualOriginalContextFibers : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (context domain codomain x y z : Nat),
  (encodedApplication n arity context domain codomain (ContextUniform.objectCode Gamma x)
      (ContextUniform.objectCode Gamma y) (ContextUniform.objectCode Gamma z) ↔
    OrdinaryArithmeticApplication.decodedApplication n arity Gamma context domain codomain x y = some z)

def ActualNoCrossContextApplications : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma Delta Xi : List Ty)
    (context domain codomain x y z : Nat),
  (Gamma ≠ Delta ∨ Gamma ≠ Xi) →
  ¬ encodedApplication n arity context domain codomain (ContextUniform.objectCode Gamma x)
    (ContextUniform.objectCode Delta y) (ContextUniform.objectCode Xi z)

/-- One actual Program 6 for all Gamma; exact original decoded application
and genuine typed source application, not computability or accessibility. -/
def ActualApplicationArithmeticFormula : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat), ∃ p : Program 6,
  (∀ v, evaluate p v = applicationValue n arity v) ∧
  (∀ context domain codomain f a z : Nat,
    (applicationFormula p).Realize ![context,domain,codomain,f,a,z] ↔
      encodedApplication n arity context domain codomain f a z) ∧
  (∀ (symbols : List (Fin n)) (S : List Ty), SubtypeClosed (fun t => t ∈ S) →
    ∀ (table : Fin n → Fin n → Bool) (Gamma : List Ty) (sigma tau : Ty)
      (f : AuxTerm (Fin n) arity Gamma (.arrow sigma tau)) (a : AuxTerm (Fin n) arity Gamma sigma),
    NumberedFiniteUniverse.InUniverse symbols S f → NumberedFiniteUniverse.InUniverse symbols S a →
    ∀ z : Nat, (applicationFormula p).Realize ![OrdinaryArithmeticQuotient.contextCode symbols S table,
      typeNumber sigma,typeNumber tau,
      ContextUniform.objectCode Gamma (representativeCode symbols S ⟨.arrow sigma tau,f⟩),
      ContextUniform.objectCode Gamma (representativeCode symbols S ⟨sigma,a⟩),
      ContextUniform.objectCode Gamma z] ↔
    representativeCode symbols S (NumberedQuotientApplication.applicationPacked f a) = z)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaApplicationTargets
