module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawEqualityInstantiationCertificate.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalDispatcherRetention.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.EqualityInstantiationRetention
open GorbowSyntax GorbowPRProgram GorbowPRRegistry SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
/-- Actual old dispatcher, with arbitrary original validity/arithmetic/source leaves. -/
abbrev original (valid old arithmetic : Program 1) (x : Program 3) : Program 4 :=
 HistoryDispatcher.lineDispatcher valid old arithmetic x
/-- The sole changed component is the literal fixed unary equality-instantiation
logical leaf: original tag13, original two annotations, unchanged rule dispatcher. -/
abbrev extended (a b : Term 1) (valid old arithmetic : Program 1) (x : Program 3) : Program 4 :=
 HistoryDispatcher.lineDispatcher valid (RawEqualityInstantiationAcceptance.logicalLeaf a b old) arithmetic x
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.EqualityInstantiationRetention
