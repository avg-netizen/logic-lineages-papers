module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuccCongruence.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawComputationSource
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPublishedDCB SixSol20261113
abbrev logical (old : Program 1) : Program 1 := RawCumulativeLogical.logical old
abbrev arithmetic (oldA : Program 1) : Program 1 := RawCumulativeArithmetic.arithmetic oldA
abbrev verifier (old oldA : Program 1) (baseX : Program 3) : Program 5 :=
 RawCumulativeLogical.verifier old (arithmetic oldA) (SaturatedAxiomLeaf.saturated baseX)
abbrev root (pF pR old oldA : Program 1) (baseX : Program 3) : Program 4 :=
 GorbowSourceRegistryPadding.root (augmented pF (verifier old oldA baseX)) pR
/-- Same six original packages, now explicitly instantiated at BOTH cumulative
leaves; no package is silently reused at an incompatible logical AST. -/
def Packages (old oldA : Program 1) (baseX : Program 3) (offset : Nat)
 (pF pR : Program 1) (c : Code) (mtag xtag : Nat) : Prop :=
 let l := logical old
 let a := arithmetic oldA
 let x := SaturatedAxiomLeaf.saturated baseX
 LiteralValidatedSource.Targets.ValidatorPackage l a x offset pF pR ∧
 LiteralSourceCoreMP.Targets.MPPackage l a x offset pF pR mtag ∧
 LiteralSourceFuelWitness.Targets.WitnessPackage l a x pF pR ∧
 SaturatedAxiomSource.Targets.AxiomPackage l a baseX pF pR xtag ∧
 SaturatedSourceMP.Targets.ClosurePackage l a baseX offset pF pR mtag ∧
 PublishedSourceHB2.Targets.HB2Package l a baseX pF pR c
/-- Finite actual AST carrier independent of all future runtime terms. -/
def items (old oldA : Program 1) (x : Program 3) : List Packed :=
 [⟨4,LiteralRawMP.constructor⟩,⟨1,RawReflexivity.lineConstructor⟩,
  ⟨1,RawAddZero.lineConstructor⟩,⟨2,RawAddSucc.lineConstructor⟩,⟨2,RawSuccReplace.lineConstructor⟩,
  ⟨2,HistoryCodec.pair⟩,⟨2,HistoryCodec.cons⟩,⟨2,HistoryAppend.append⟩,
  ⟨1,TwoSol20261113.ReflexivityRecognizer.termValidator⟩,
  ⟨2,LiteralSyntaxValidator.formulaValidator⟩,⟨1,LiteralSyntaxValidator.lineValidator⟩,
  ⟨1,logical old⟩,⟨1,arithmetic oldA⟩,
  ⟨4,RawCumulativeLogical.dispatcher old (arithmetic oldA) x⟩,
  ⟨4,SixSol20261112.HistoryMachine.iterator (RawCumulativeLogical.kernel old (arithmetic oldA) x)⟩,
  ⟨5,RawCumulativeLogical.checker old (arithmetic oldA) x⟩,
  ⟨1,HistoryLengthOffset.lengthProgram⟩,⟨1,HistoryDecoder.decoder true⟩,
  ⟨2,HistoryLookup.drop⟩,⟨2,HistoryLookup.lookup⟩]
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawComputationSource
