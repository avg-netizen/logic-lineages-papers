module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedAxiomSource.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedVerifierMP.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedSourceMP
open GorbowSyntax SixSol20261112.Fuel
/-- Actual core fuel monotonicity, all six original terms internal. -/
def coreMonotonicityClause (qtag : Nat) : Sentence :=
 GorbowStandardInduction.universalClosure
  (.imp (orderGuard (.var 1 : Term 6) (.var 2))
   (.imp (SaturatedCoreFuel.acceptance qtag (.var 0) (.var 1) (.var 3) (.var 4) (.var 5))
    (SaturatedCoreFuel.acceptance qtag (.var 0) (.var 2) (.var 3) (.var 4) (.var 5))))
/-- Actual outer/core equivalence at the same current bound. -/
def equivalenceClause (vtag qtag : Nat) : Sentence :=
 GorbowStandardInduction.universalClosure
  (SaturatedVerifierCore.equivalence vtag qtag (.var 0 : Term 5) (.var 1) (.var 2) (.var 3) (.var 4))
/-- Raw certificate MP for two independent outer fuels at common sum bound.
This is not rho-to-sigma implication distribution or source HB2/HB3. -/
def outerMPClause (vtag atag ctag mtag : Nat) : Sentence :=
 GorbowStandardInduction.universalClosure
  (SaturatedVerifierMP.preservation vtag atag ctag mtag
   (.var 0 : Term 8) (.var 1) (.var 2) (.var 3) (.var 4) (.var 5) (.var 6) (.var 7))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedSourceMP
