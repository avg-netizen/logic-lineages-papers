module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawReflexivitySource.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddZeroCertificate.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawJointSource
open GorbowPRProgram GorbowPRRegistry SixSol20261113
/-- Both calibrated leaves are selected before the source. One finite carrier
contains the original logical interface plus the actual add-zero constructor
and refined arithmetic leaf; it is independent of all runtime terms. -/
def items (old oldA : Program 1) (x : Program 3) : List Packed :=
 RawReflexivitySource.items old (RawAddZero.arithmeticLeaf oldA) x ++
 [⟨1,RawAddZero.lineConstructor⟩,⟨1,RawAddZero.arithmeticLeaf oldA⟩]
abbrev root (pF pR old oldA : Program 1) (baseX : Program 3) : Program 4 :=
 ReflexivityInstalled.root pF pR old (RawAddZero.arithmeticLeaf oldA) baseX
abbrev verifier (old oldA : Program 1) (baseX : Program 3) : Program 5 :=
 ReflexivityInstalled.verifier old (RawAddZero.arithmeticLeaf oldA) baseX
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawJointSource
