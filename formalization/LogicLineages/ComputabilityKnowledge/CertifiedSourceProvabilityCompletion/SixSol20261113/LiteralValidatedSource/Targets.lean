module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralValidatedSource.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralValidatedSource.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB List.Vector
open SixSol20261112 LiteralCheckerAuxiliaries
/-- All addresses are structural functions of the NEW tuple, including the
actual history-kernel validity child and its actual formula/scanner descendants.
The source clauses are genuine internal derivations in the identical S. -/
def ValidatorPackage (logical arithmetic : Program 1) (axiomProgram : Program 3)
 (appendOffset : Nat) (pF pR : Program 1) : Prop :=
 let k := HistoryKernel.kernel valid logical arithmetic axiomProgram
 let q := LiteralKernelSource.verifier valid logical arithmetic axiomProgram bound initial finalizer
 let root := GorbowSourceRegistryPadding.root (augmented pF q) pR
 let vtag := validityTag pF logical arithmetic axiomProgram
 let ftag := formulaTag vtag
 let atag := LiteralKernelSource.appendTag pF valid logical arithmetic axiomProgram bound initial finalizer appendOffset
 let ptag := LiteralKernelSource.pairTag pF valid logical arithmetic axiomProgram bound initial finalizer
 let ctag := LiteralKernelSource.consTag pF valid logical arithmetic axiomProgram bound initial finalizer
 (nodes root)[iteratorTag pF logical arithmetic axiomProgram]? = some ⟨4,SixSol20261112.HistoryMachine.iterator k⟩ ∧
 (nodes root)[vtag]? = some ⟨1,LiteralSyntaxValidator.lineValidator⟩ ∧
 (nodes root)[ftag]? = some ⟨2,LiteralSyntaxValidator.formulaValidator⟩ ∧
 (nodes root)[leftTag vtag]? = some ⟨1,HistoryDecoder.decoder false⟩ ∧
 (nodes root)[rightTag vtag]? = some ⟨1,HistoryDecoder.decoder true⟩ ∧
 (nodes root)[scanTag vtag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩ ∧
 (nodes root)[equalityTag vtag]? = some ⟨2,HistoryRuleSuffix.equalCode⟩ ∧
 (nodes root)[taskConsTag vtag]? = some ⟨2,HistoryCodec.cons⟩ ∧
 (nodes root)[taskPairTag vtag]? = some ⟨2,HistoryCodec.pair⟩ ∧
 Nonempty (Derivation (S pF pR q) (booleanClause ftag)) ∧
 Nonempty (Derivation (S pF pR q) (lineClause vtag ftag ptag)) ∧
 Nonempty (Derivation (S pF pR q) (implicationClause ftag atag ctag)) ∧
 Nonempty (Derivation (S pF pR q) (quantifierClause ftag ctag 10)) ∧
 Nonempty (Derivation (S pF pR q) (quantifierClause ftag ctag 11)) ∧
 Nonempty (Derivation (S pF pR q) (scanFusionClause (scanTag vtag) atag)) ∧
 Nonempty (Derivation (S pF pR q) (scanFrameClause (scanTag vtag) atag))

/-- A fresh complete tuple, with validity fixed OUTSIDE all existential choices.
All previous retained contracts and new internal validator/scanner clauses live
at this SAME tuple. Not original tuple identity, certificate closure or HB. -/
def SameSourceValidatedAuxiliaries : Prop :=
 ∃ (logical arithmetic : Program 1) (axiomProgram : Program 3) (appendOffset : Nat),
 ∃ (pF pR : Program 1) (c : Code) (tagCK : Nat) (pCK : Program 2) (tagG : Nat) (pG : Program 6),
 Retained logical arithmetic axiomProgram appendOffset pF pR c tagCK pCK tagG pG ∧
 ValidatorPackage logical arithmetic axiomProgram appendOffset pF pR
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralValidatedSource.Targets
