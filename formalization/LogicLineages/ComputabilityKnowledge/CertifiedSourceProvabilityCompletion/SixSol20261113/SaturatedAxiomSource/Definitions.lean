module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSourceFuelWitness.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedAxiomLeaf.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedAxiomSource
open GorbowSyntax SixSol20261112
/-- Monotonicity of the actual saturated axiom leaf at its installed address,
with all four runtime parameters genuinely internally quantified. This does
not assert dispatcher, kernel, core or outer-MP monotonicity. -/
def axiomMonotonicityClause (xtag : Nat) : Sentence :=
 GorbowStandardInduction.universalClosure
  (.imp (Fuel.orderGuard (.var 1 : Term 4) (.var 2))
   (.imp (SaturatedAxiomLeaf.success xtag (.var 0) (.var 1) (.var 3))
    (SaturatedAxiomLeaf.success xtag (.var 0) (.var 2) (.var 3))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedAxiomSource
