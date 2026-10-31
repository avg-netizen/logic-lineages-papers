module
public import LogicLineages.OrdinalComparison.WWPolicyAssignmentDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.LiteralPolicy

/-- A deliberately refusing exact symbolic evaluator for the five finite-tail
collapse atoms occurring in the printed closed witness. It never approximates
collapse, evaluates a huge control value, or normalizes the source term. -/
structure WitnessPolynomial where
  constant : Nat
  at6 : Nat
  at8 : Nat
  at14 : Nat
  at18 : Nat
  at20 : Nat
  deriving DecidableEq

def WitnessPolynomial.add (a b : WitnessPolynomial) : WitnessPolynomial :=
  ⟨a.constant + b.constant, a.at6 + b.at6, a.at8 + b.at8,
    a.at14 + b.at14, a.at18 + b.at18, a.at20 + b.at20⟩

noncomputable def witnessH (n : Nat) : Nat := actualCollapse (Ordinal.omega0 + (n : Ordinal))

noncomputable def WitnessPolynomial.value (a : WitnessPolynomial) : Nat :=
  a.constant + a.at6 * witnessH 6 + a.at8 * witnessH 8 +
    a.at14 * witnessH 14 + a.at18 * witnessH 18 + a.at20 * witnessH 20

def witnessAtom : Nat → Option WitnessPolynomial
  | 6 => some ⟨0, 1, 0, 0, 0, 0⟩
  | 8 => some ⟨0, 0, 1, 0, 0, 0⟩
  | 14 => some ⟨0, 0, 0, 1, 0, 0⟩
  | 18 => some ⟨0, 0, 0, 0, 1, 0⟩
  | 20 => some ⟨0, 0, 0, 0, 0, 1⟩
  | _ => none

def witnessPolynomial {ι : Type} :
    LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics.Term ι → Option WitnessPolynomial
  | .one => some ⟨1, 0, 0, 0, 0, 0⟩
  | .add a b => do
      let x ← witnessPolynomial a
      let y ← witnessPolynomial b
      pure (x.add y)
  | .collapse a b => do
      let head ← finiteAddValue a
      let tail ← finiteAddValue b
      if head = 1 then witnessAtom tail else none
  | _ => none

def witnessScalar (p : ActiveSumAssociation) : Option (OrdinalExpression []) := do
  let v ← assignment p witness
  pure (v 0)

def witnessLeftPolynomial : WitnessPolynomial := ⟨3880, 1, 10, 388, 0, 3880⟩
def witnessRightPolynomial : WitnessPolynomial := ⟨3480, 1, 10, 348, 3480, 0⟩

end LogicLineages.OrdinalComparison.Source.LiteralPolicy
