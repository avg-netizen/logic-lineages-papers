module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralValidatedSource.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCoreMP.Targets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryAppend.ValueEquationsProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSourceCoreMP
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB List.Vector
open SixSol20261112 LiteralCheckerAuxiliaries HistoryRuleSuffix
/-- All addresses below refer to the fresh tuple whose validity leaf is fixed
before existential choices. No address of an older tuple is retained by fiat. -/
abbrev valid := LiteralValidatedSource.valid

def coreTag (pF : Program 1) (l a : Program 1) (x : Program 3) : Nat :=
 LiteralCheckerAuxiliaries.coreTag pF valid l a x
def dispatcherTag (pF : Program 1) (l a : Program 1) (x : Program 3) : Nat :=
 HistoryKernel.TransitionEquationsProof.dispatcherTag
  (LiteralKernelSource.kernelTag pF valid l a x bound initial finalizer) valid l a x
/-- Exact length-function child of the actual literal scanner's finalState. -/
def lengthTag (stag : Nat) : Nat :=
 let ftag := stag + argumentTag (HistoryDecoder.decoder true)
  (fun _ : Fin 1 => LiteralSyntaxScan.finalState) 0
 let fs : Fin 2 → Program 2 := Fin.cases
  (applyOne HistoryLengthOffset.lengthProgram (.projection 1))
  (Fin.cases LiteralSyntaxScan.initial Fin.elim0)
 ftag + argumentTag LiteralSyntaxScan.iterator fs 0 + 1
/-- The lookup subtree really occurs in append's course-of-values table. -/
def lookupTag (atag : Nat) : Nat :=
 HistoryAppend.ValueEquationsProof.lookupWrapper
  (HistoryAppend.TableEquationsProof.valueTag
    (HistoryAppend.AppendEquationsProof.tableTag atag)) + 1
/-- Actual drop child of that lookup, not an assumed new installation. -/
def dropTag (atag : Nat) : Nat := HistoryLookup.LookupProof.dropTag (lookupTag atag)

def coreMPClause (qtag atag ctag mtag : Nat) : Sentence :=
 GorbowStandardInduction.universalClosure
  (.imp (LiteralCoreMP.inputAcceptance qtag atag ctag
    (.var (0 : Fin 7)) (.var 1) (.var 2) (.var 3) (.var 4) (.var 5) (.var 6))
   (.equal (LiteralCheckerAcceptance.coreCall qtag (.var 5) (.var 6) (.var 0)
     (.add (.var 2) (.var 2))
     (LiteralMPRun.certificate mtag (.var 0) (.var 2) (.var 3) (.var 4))) (.succ .zero)))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSourceCoreMP
