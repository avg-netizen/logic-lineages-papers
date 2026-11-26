module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawCumulativeArithmetic.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawThreeSource
open GorbowPRProgram GorbowPRRegistry SixSol20261113
/-- One runtime-independent finite carrier includes all three original line
constructors and the actual nested arithmetic leaf. -/
def items (old oldA : Program 1) (x : Program 3) : List Packed :=
 RawReflexivitySource.items old (RawCumulativeArithmetic.arithmetic oldA) x ++
 [⟨1,RawAddZero.lineConstructor⟩,⟨2,RawAddSucc.lineConstructor⟩,
  ⟨1,RawCumulativeArithmetic.arithmetic oldA⟩]
abbrev root (pF pR old oldA : Program 1) (baseX : Program 3) : Program 4 :=
 ReflexivityInstalled.root pF pR old (RawCumulativeArithmetic.arithmetic oldA) baseX
abbrev verifier (old oldA : Program 1) (baseX : Program 3) : Program 5 :=
 ReflexivityInstalled.verifier old (RawCumulativeArithmetic.arithmetic oldA) baseX
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawThreeSource
