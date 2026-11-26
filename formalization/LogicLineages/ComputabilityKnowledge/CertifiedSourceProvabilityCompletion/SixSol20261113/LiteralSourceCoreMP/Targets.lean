module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSourceCoreMP.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSourceCoreMP.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB
open LiteralCheckerAuxiliaries
/-- Additional actual nodes and internal core-MP closure at ONE newly built
source. The canonical constructor is installed in the root before the source
index is chosen. All other addresses are exact structural descendants. -/
def MPPackage (l a : Program 1) (x : Program 3) (offset : Nat)
 (pF pR : Program 1) (mtag : Nat) : Prop :=
 let q := LiteralKernelSource.verifier valid l a x bound initial finalizer
 let root := GorbowSourceRegistryPadding.root (augmented pF q) pR
 let atag := LiteralKernelSource.appendTag pF valid l a x bound initial finalizer offset
 let ctag := LiteralKernelSource.consTag pF valid l a x bound initial finalizer
 let stag := LiteralValidatedSource.scanTag (LiteralValidatedSource.validityTag pF l a x)
 (nodes root)[mtag]? = some ⟨4,LiteralRawMP.constructor⟩ ∧
 (nodes root)[coreTag pF l a x]? = some ⟨5,LiteralKernelSource.coreChecker valid l a x bound initial finalizer⟩ ∧
 (nodes root)[dispatcherTag pF l a x]? = some ⟨4,HistoryDispatcher.lineDispatcher valid l a x⟩ ∧
 (nodes root)[lengthTag stag]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩ ∧
 (nodes root)[lookupTag atag]? = some ⟨2,HistoryLookup.lookup⟩ ∧
 (nodes root)[dropTag atag]? = some ⟨2,HistoryLookup.drop⟩ ∧
 Nonempty (Derivation (S pF pR q) (coreMPClause (coreTag pF l a x) atag ctag mtag))

/-- Fresh source extension, retaining the ENTIRE two previously accepted
packages literally at the SAME witnesses. The new clause uses only the two
actual input core acceptances; no successful-run or new-line-validity premise
is added. This is core closure, not outer fuel-verifier closure or HB2/HB3. -/
def SameSourceCoreMP : Prop :=
 ∃ (l a : Program 1) (x : Program 3) (offset : Nat),
 ∃ (pF pR : Program 1) (c : Code) (tagCK : Nat) (pCK : Program 2)
   (tagG : Nat) (pG : Program 6) (mtag : Nat),
 LiteralValidatedSource.Retained l a x offset pF pR c tagCK pCK tagG pG ∧
 LiteralValidatedSource.Targets.ValidatorPackage l a x offset pF pR ∧
 MPPackage l a x offset pF pR mtag
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSourceCoreMP.Targets
