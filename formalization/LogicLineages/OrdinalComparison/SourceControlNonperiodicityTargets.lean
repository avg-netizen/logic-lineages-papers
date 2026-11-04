module
public import LogicLineages.OrdinalComparison.SourceControlNonperiodicityDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.SourceControlNonperiodicity.Targets

def EffectiveBoundedSimulation : Prop :=
  Primrec program ∧ Primrec boundedH ∧
  (∀ c : Nat.Partrec.Code, program (Encodable.encode c) = c) ∧
  (∀ e : Nat, (Nat.Partrec.Code.eval (program e) 0).Dom ↔ ∃ t : Nat, boundedH (e,t) = true) ∧
  (∀ e t u : Nat, t ≤ u → boundedH (e,t) = true → boundedH (e,u) = true)

def ExactControlParity : Prop :=
  ∀ b : Nat, Primrec (gamma b) ∧ ∀ n : Nat, b < n →
    gamma b n % 2 = if boundedH (PerturbedControl.valuationTwo n,n) then 1 else 0

def ExactValuationFibers : Prop :=
  Primrec (fun z : Nat × Nat × Nat => fiberBase z.1 z.2.1 z.2.2) ∧
  ∀ N b p e k : Nat, 0 < p →
    max N b < fiberPoint N b p e k ∧
    PerturbedControl.valuationTwo (fiberPoint N b p e k) = e ∧
    fiberPoint N b p e k % p = fiberBase N b e % p ∧
    k ≤ fiberPoint N b p e k

def NonEventualPeriodicity : Prop := ∀ b : Nat, ¬ EventuallyPeriodicParity b
end LogicLineages.OrdinalComparison.SourceControlNonperiodicity.Targets
