module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionErasure.TickCasesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionErasure.LogicProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
def property {ctx : Nat} (etag ntag otag : Nat) (state raw : Term ctx) : Formula ctx :=
 .equal (eraseCall etag (newTickCall ntag state raw)) (oldTickCall otag (eraseCall etag state))
def packedProperty {ctx : Nat} (etag ntag otag ptag : Nat) (tokens state out raw : Term ctx) : Formula ctx :=
 property etag ntag otag (HistoryKernel.pairCall ptag tokens (HistoryKernel.pairCall ptag state out)) raw
theorem substProperty {m n : Nat} (s : Fin m → Term n) etag ntag otag (state raw : Term m) :
 substituteFormula s (property etag ntag otag state raw) =
 property etag ntag otag (substitute s state) (substitute s raw) := by
 simp only [property,eraseCall,newTickCall,oldTickCall,substituteFormula,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil]
theorem substPacked {m n : Nat} (s : Fin m → Term n) etag ntag otag ptag (tokens state out raw : Term m) :
 substituteFormula s (packedProperty etag ntag otag ptag tokens state out raw) =
 packedProperty etag ntag otag ptag (substitute s tokens) (substitute s state) (substitute s out) (substitute s raw) := by
 simp only [packedProperty,substProperty,HistoryKernel.pairCall,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil]
theorem weakenPacked {ctx : Nat} etag ntag otag ptag (tokens state out raw : Term ctx) :
 GorbowPACore.weaken (packedProperty etag ntag otag ptag tokens state out raw) =
 packedProperty etag ntag otag ptag (liftTerm tokens) (liftTerm state) (liftTerm out) (liftTerm raw) := by
 rw [GorbowPACore.weaken,substPacked]
 rfl
noncomputable def transport {T : Sentence → Prop} {ctx : Nat} etag ntag otag (a b raw : Term ctx) :
 Derivation T (.imp (.equal a b) (.imp (property etag ntag otag a raw) (property etag ntag otag b raw))) := by
 have h := Derivation.logical (A := T) (.equalityReplace (property etag ntag otag (.var 0) (liftTerm raw)) a b)
 simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substProperty,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using h
noncomputable def transportPacked {T : Sentence → Prop} {ctx : Nat} etag ntag otag ptag (a b state out raw : Term ctx) :
 Derivation T (.imp (.equal a b)
  (.imp (packedProperty etag ntag otag ptag a state out raw) (packedProperty etag ntag otag ptag b state out raw))) := by
 have h := Derivation.logical (A := T) (.equalityReplace
  (packedProperty etag ntag otag ptag (.var 0) (liftTerm state) (liftTerm out) (liftTerm raw)) a b)
 simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substPacked,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using h
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionErasure.LogicProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionErasure.LogicProof
