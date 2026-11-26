module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.SubstitutionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.WitnessProof
open GorbowSyntax GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport SubstitutionProof HistoryOrder.SupportProof
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
theorem substBody {m n : Nat} (s : Fin m → Term n) stag len q l r (nt chunk oldResult newResult : Term m) :
 substituteFormula s (resultBody stag len q l r nt chunk oldResult newResult) =
 resultBody stag len q l r (substitute s nt) (substitute s chunk) (substitute s oldResult) (substitute s newResult) := by
 simp only [resultBody,substituteFormula,substStack,LiteralSyntaxScan.scanCall,Logic.substCall,
  List.Vector.map_cons,List.Vector.map_nil,substitute]
theorem bodyAt {ctx : Nat} stag len q l r (nt chunk oldResult newResult : Term ctx) :
 GorbowStandardInstances.instantiate
  (resultBody stag len q l r (liftTerm nt) (liftTerm chunk) (liftTerm oldResult) (.var 0)) newResult =
 resultBody stag len q l r nt chunk oldResult newResult := by
 simp only [GorbowStandardInstances.instantiate,substBody,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]
noncomputable def introResult {T : Sentence → Prop} {ctx : Nat} stag len q l r
 (nt chunk oldResult newResult : Term ctx) :
 Derivation T (.imp (resultBody stag len q l r nt chunk oldResult newResult)
  (results stag len q l r nt chunk oldResult)) := by
 have h := existsIntroRule (T := T)
  (resultBody stag len q l r (liftTerm nt) (liftTerm chunk) (liftTerm oldResult) (.var 0)) newResult
 rw [bodyAt] at h
 exact h
theorem substResults {m n : Nat} (s : Fin m → Term n) stag len q l r (nt chunk oldResult : Term m) :
 substituteFormula s (results stag len q l r nt chunk oldResult) =
 results stag len q l r (substitute s nt) (substitute s chunk) (substitute s oldResult) := by
 simp only [results,substituteFormula,substBody,substituteLift,substitute,liftSubstitute,Fin.cases_zero]
def property {ctx : Nat} (etag vtag stepTag stag len q l r : Nat) (ot nt tok result raw : Term ctx) : Formula ctx :=
 .imp (RawReflexivityDispatcher.valid vtag raw)
  (.imp (stackRelation len q l r ot nt)
   (.imp (.equal (LiteralSyntaxStep.stepCall stepTag (.succ ot) tok) (.succ result))
    (results stag len q l r nt (UniformClosedSubstitutionEmit.emitCall etag (.succ ot) tok raw) result)))
theorem substProperty {m n : Nat} (s : Fin m → Term n) etag vtag stepTag stag len q l r
 (ot nt tok result raw : Term m) :
 substituteFormula s (property etag vtag stepTag stag len q l r ot nt tok result raw) =
 property etag vtag stepTag stag len q l r (substitute s ot) (substitute s nt)
  (substitute s tok) (substitute s result) (substitute s raw) := by
 simp only [property,substituteFormula,substStack,substResults,LiteralSyntaxStep.stepCall,
  UniformClosedSubstitutionEmit.emitCall,RawReflexivityDispatcher.valid,
  TwoSol20261113.ReflexivityRecognizer.leafCall,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,substitute]
theorem weakenProperty {ctx : Nat} etag vtag stepTag stag len q l r (ot nt tok result raw : Term ctx) :
 GorbowPACore.weaken (property etag vtag stepTag stag len q l r ot nt tok result raw) =
 property etag vtag stepTag stag len q l r (liftTerm ot) (liftTerm nt) (liftTerm tok) (liftTerm result) (liftTerm raw) := by
 rw [GorbowPACore.weaken,substProperty]
 rfl
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.WitnessProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.WitnessProof
