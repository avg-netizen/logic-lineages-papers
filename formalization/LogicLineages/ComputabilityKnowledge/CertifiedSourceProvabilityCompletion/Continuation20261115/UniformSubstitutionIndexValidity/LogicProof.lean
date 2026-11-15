module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionIndexValidity.BranchProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionIndexValidity.AboveProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionIndexValidity.LogicProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
def outputValid {ctx : Nat} (etag stag ptag ctag : Nat) (index depth rest raw : Term ctx) : Formula ctx :=
 .equal (LiteralSyntaxScan.scanCall stag (termTasks ptag ctag depth)
  (UniformClosedSubstitutionEmit.emitCall etag
   (UniformClosedSubstitutionEmit.stateValue ptag ctag (Term.numeral 2) (.succ depth) rest) index raw)) (.succ .zero)
def claim {ctx : Nat} (etag vtag stag ptag ctag dtag : Nat) (index depth positive rest raw : Term ctx) : Formula ctx :=
 .imp (RawReflexivityDispatcher.valid vtag raw)
  (.imp (.equal (HistoryDifference.differenceCall dtag index (.succ depth)) (.succ positive))
   (outputValid etag stag ptag ctag index depth rest raw))
theorem substOutput {m n : Nat} (s : Fin m → Term n) etag stag ptag ctag (index depth rest raw : Term m) :
 substituteFormula s (outputValid etag stag ptag ctag index depth rest raw) =
 outputValid etag stag ptag ctag (substitute s index) (substitute s depth) (substitute s rest) (substitute s raw) := by
 simp only [outputValid,termTasks,FullFormulaInstantiationValidity.ClosedTermDepthTargets.tasks,
  LiteralSyntaxStep.taskCall,LiteralSyntaxScan.scanCall,UniformClosedSubstitutionEmit.emitCall,
  UniformClosedSubstitutionEmit.stateValue,HistoryLookup.consCall,HistoryKernel.pairCall,
  substituteFormula,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,substitute,
  LiteralSyntaxStep.ExpansionSupportProof.substituteNumeral]
theorem substClaim {m n : Nat} (s : Fin m → Term n) etag vtag stag ptag ctag dtag
 (index depth positive rest raw : Term m) :
 substituteFormula s (claim etag vtag stag ptag ctag dtag index depth positive rest raw) =
 claim etag vtag stag ptag ctag dtag (substitute s index) (substitute s depth)
  (substitute s positive) (substitute s rest) (substitute s raw) := by
 simp only [claim,substituteFormula,substOutput,RawReflexivityDispatcher.valid,TwoSol20261113.ReflexivityRecognizer.leafCall,
  HistoryDifference.differenceCall,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,substitute]
noncomputable def transportIndex {T : Sentence → Prop} {ctx : Nat} etag stag ptag ctag (a b depth rest raw : Term ctx) :
 Derivation T (.imp (.equal a b)
  (.imp (outputValid etag stag ptag ctag a depth rest raw) (outputValid etag stag ptag ctag b depth rest raw))) := by
 have h := Derivation.logical (A := T) (.equalityReplace
  (outputValid etag stag ptag ctag (.var 0) (liftTerm depth) (liftTerm rest) (liftTerm raw)) a b)
 simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substOutput,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using h
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionIndexValidity.LogicProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionIndexValidity.LogicProof
