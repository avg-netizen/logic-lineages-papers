module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawReflexivityCertificate.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawReflexivitySource
open GorbowPRProgram GorbowPRRegistry SixSol20261113
/-- One finite list of literal ASTs, independent of every future raw term,
index and fuel. The complete semantic producer remains separately installed. -/
def items (old a : Program 1) (x : Program 3) : List Packed :=
 [⟨4,LiteralRawMP.constructor⟩,
  ⟨1,RawReflexivity.lineConstructor⟩,
  ⟨2,HistoryCodec.pair⟩,⟨2,HistoryCodec.cons⟩,⟨2,HistoryAppend.append⟩,
  ⟨1,TwoSol20261113.ReflexivityRecognizer.termValidator⟩,
  ⟨2,LiteralSyntaxValidator.formulaValidator⟩,
  ⟨1,TwoSol20261113.ReflexivityCertificate.validity⟩,
  ⟨1,TwoSol20261113.ReflexivityCertificate.logical old⟩,
  ⟨4,TwoSol20261113.ReflexivityCertificate.dispatcher old a x⟩,
  ⟨4,SixSol20261112.HistoryMachine.iterator (TwoSol20261113.ReflexivityCertificate.kernel old a x)⟩,
  ⟨5,TwoSol20261113.ReflexivityCertificate.checker old a x⟩]
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawReflexivitySource
