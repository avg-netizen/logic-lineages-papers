module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSourceCoreMP.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.FuelWitness.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSourceFuelWitness
open GorbowSyntax SixSol20261112.Fuel
/-- Actual bounded core witness extraction, universally closed over all five
original inputs. This does not identify core witnesses from different runs. -/
def extractionClause (vtag qtag : Nat) : Sentence :=
 GorbowStandardInduction.universalClosure
  (.imp (success vtag (.var 0 : Term 5) (.var 1) (.var 2) (.var 3) (.var 4))
   (FuelWitness.boundedCore qtag (.var 0) (.var 1) (.var 2) (.var 3) (.var 4)))
/-- Actual converse at the same outer bound, with an internal existential
core-fuel witness; no core-fuel monotonicity is asserted. -/
def injectionClause (vtag qtag : Nat) : Sentence :=
 GorbowStandardInduction.universalClosure
  (.imp (FuelWitness.boundedCore qtag (.var 0 : Term 5) (.var 1) (.var 2) (.var 3) (.var 4))
   (success vtag (.var 0) (.var 1) (.var 2) (.var 3) (.var 4)))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSourceFuelWitness
