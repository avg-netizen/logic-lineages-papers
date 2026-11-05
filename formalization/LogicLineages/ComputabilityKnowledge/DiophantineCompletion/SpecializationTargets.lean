module
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.SpecializationDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.DiophantineCompletion.SpecializationTargets
open PolynomialCircuit Specialization DiophantinePolynomialBridge

/-- Exact interpretation in the original integer polynomial ring, with
natural parameter x and arbitrary integer valuations of the remaining inputs. -/
def SubstitutionIdentity : Prop := ∀ (p : Code) (x : Nat) (ρ : Nat → Int),
  MvPolynomial.eval ρ (interpret (specialize x p)) =
    MvPolynomial.eval (fun i => Nat.casesOn i (x : Int) ρ) (interpret p)

def SubstitutionWellFormed : Prop := ∀ (p : Code) (x : Nat),
  p.WellFormed → (specialize x p).WellFormed

/-- Exact zero-allowing natural witness correspondence, retaining the
original first-parameter and auxiliary-witness convention. -/
def SubstitutionRootCorrespondence : Prop := ∀ (p : Code) (m x : Nat),
  p.inputCount = m + 1 →
  (PolynomialDomainShift.HasNonnegativeRoot (specialize x p) ↔
    ∃ w : Fin m → Nat, MvPolynomial.eval
      (fun i => (joinedNat (fun _ : Fin 1 => x) w i : Int)) (interpret p) = 0)

def SpecializationCodeCalibration : Prop := ∀ (p : Code) (x : Nat),
  specializationCode p x = Encodable.encode (PolynomialCircuit.encode (specialize x p))

/-- Effectiveness only for explicit fixed finite codes. There is no claimed
algorithm choosing that code from an extensional representation theorem. -/
def SpecializationCodePrimrec : Prop := ∀ p : Code, Primrec (specializationCode p)

end LogicLineages.ComputabilityKnowledge.DiophantineCompletion.SpecializationTargets
