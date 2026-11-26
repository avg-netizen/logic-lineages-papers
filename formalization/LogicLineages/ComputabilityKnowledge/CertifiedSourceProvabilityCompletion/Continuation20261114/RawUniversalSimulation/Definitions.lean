module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalStateRetention.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorSuffix.RelationProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalSimulation
open GorbowSyntax SixSol20261113 SixSol20261112.Fuel
/-- Equality on every successful old state; no condition on failed old states. -/
def body {ctx : Nat} (ptag : Nat) (old new h lines : Term ctx) : Formula ctx :=
 .imp (.equal old (HistoryKernel.pairCall ptag (.succ h) lines))
       (.equal new (HistoryKernel.pairCall ptag (.succ h) lines))
def inner {ctx : Nat} (ptag : Nat) (old new h : Term ctx) : Formula ctx :=
 .all (body ptag (liftTerm old) (liftTerm new) (liftTerm h) (.var 0))
def relation {ctx : Nat} (ptag : Nat) (old new : Term ctx) : Formula ctx :=
 .all (inner ptag (liftTerm old) (liftTerm new) (.var 0))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalSimulation
