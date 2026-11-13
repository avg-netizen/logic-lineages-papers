module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.Fuel.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.Fuel.InductionStatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.FuelWitness
open GorbowSyntax
open SixSol20261112.Fuel
/-- A genuine INTERNAL bounded core-fuel witness. The outer existential binds
an actual core fuel; orderGuard then binds its own additive gap witness.
All original input terms remain inside both binders by the usual lifting. -/
def boundedCore {ctx : Nat} (qtag : Nat)
 (index fuel context formula certificate : Term ctx) : Formula ctx :=
 .ex (.conj (orderGuard (.var 0) (liftTerm fuel))
  (success qtag (liftTerm index) (.var 0) (liftTerm context)
    (liftTerm formula) (liftTerm certificate)))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.FuelWitness
