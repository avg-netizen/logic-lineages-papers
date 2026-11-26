module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionFoldTransport.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionFoldTransport.InvariantProof
open GorbowSyntax GorbowTheoryProof GorbowPRDefiningEquations GorbowSubstitution GorbowFormulaSubstitution SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open UniformSubstitutionChunkTransport
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
/-- Actual final output projection with arbitrary initial accumulated output. -/
def outputAt {ctx : Nat} (ftag ptag rtag : Nat) (tokens oldTasks out raw : Term ctx) : Term ctx :=
 call rtag (UniformClosedSubstitutionRawFold.foldCall ftag tokens
  (HistoryKernel.pairCall ptag (.succ oldTasks) out) raw ::ᵥ nil)
theorem substOutput {m n : Nat} (s : Fin m → Term n) ftag ptag rtag (tokens oldTasks out raw : Term m) :
 substitute s (outputAt ftag ptag rtag tokens oldTasks out raw) =
 outputAt ftag ptag rtag (substitute s tokens) (substitute s oldTasks) (substitute s out) (substitute s raw) := by
 simp only [outputAt,UniformClosedSubstitutionRawFold.foldCall,HistoryKernel.pairCall,Logic.substCall,
  List.Vector.map_cons,List.Vector.map_nil,substitute]
/-- Strengthened induction invariant. The prefix scan is internal and is
discharged using the empty-prefix law at the final endpoint. -/
def property {ctx : Nat} (ftag vtag stag ptag len q l r : Nat)
 (tokens start raw oldTasks current out oldResult : Term ctx) : Formula ctx :=
 .imp (RawReflexivityDispatcher.valid vtag raw)
  (.imp (stackRelation len q l r oldTasks current)
   (.imp (.equal (LiteralSyntaxScan.scanCall stag start out) (.succ current))
    (.imp (.equal (LiteralSyntaxScan.scanCall stag oldTasks tokens) (.succ oldResult))
     (results stag len q l r start (outputAt ftag ptag r tokens oldTasks out raw) oldResult))))
theorem substProperty {m n : Nat} (s : Fin m → Term n) ftag vtag stag ptag len q l r
 (tokens start raw oldTasks current out oldResult : Term m) :
 substituteFormula s (property ftag vtag stag ptag len q l r tokens start raw oldTasks current out oldResult) =
 property ftag vtag stag ptag len q l r (substitute s tokens) (substitute s start) (substitute s raw)
  (substitute s oldTasks) (substitute s current) (substitute s out) (substitute s oldResult) := by
 simp only [property,substituteFormula,UniformSubstitutionChunkTransport.SubstitutionProof.substStack,
  UniformSubstitutionChunkTransport.WitnessProof.substResults,substOutput,LiteralSyntaxScan.scanCall,
  RawReflexivityDispatcher.valid,TwoSol20261113.ReflexivityRecognizer.leafCall,Logic.substCall,
  List.Vector.map_cons,List.Vector.map_nil,substitute]
theorem weakenProperty {ctx : Nat} ftag vtag stag ptag len q l r
 (tokens start raw oldTasks current out oldResult : Term ctx) :
 GorbowPACore.weaken (property ftag vtag stag ptag len q l r tokens start raw oldTasks current out oldResult) =
 property ftag vtag stag ptag len q l r (liftTerm tokens) (liftTerm start) (liftTerm raw)
  (liftTerm oldTasks) (liftTerm current) (liftTerm out) (liftTerm oldResult) := by
 rw [GorbowPACore.weaken,substProperty]
 rfl
noncomputable def transportTokens {T : Sentence → Prop} {ctx : Nat} ftag vtag stag ptag len q l r
 (a b start raw oldTasks current out oldResult : Term ctx) :
 Derivation T (.imp (.equal a b)
  (.imp (property ftag vtag stag ptag len q l r a start raw oldTasks current out oldResult)
   (property ftag vtag stag ptag len q l r b start raw oldTasks current out oldResult))) := by
 have h := Derivation.logical (A := T) (.equalityReplace
  (property ftag vtag stag ptag len q l r (.var 0) (liftTerm start) (liftTerm raw)
   (liftTerm oldTasks) (liftTerm current) (liftTerm out) (liftTerm oldResult)) a b)
 simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substProperty,
  substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using h
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionFoldTransport.InvariantProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionFoldTransport.InvariantProof
