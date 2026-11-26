module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNegatedInstanceBridge.InlineFrame.TickCasesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNegatedInstanceBridge.InlineFrame.LogicProof
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport TransformProof
def property {ctx : Nat} (ptag atag ltag rtag ttag : Nat) (prefixCode packed raw : Term ctx) : Formula ctx :=
 .equal (UniformSubstitutionErasure.newTickCall ttag (transformed ptag atag ltag rtag prefixCode packed) raw)
  (transformed ptag atag ltag rtag prefixCode (UniformSubstitutionErasure.newTickCall ttag packed raw))
def packedProperty {ctx : Nat} (ptag atag ltag rtag ttag : Nat) (prefixCode tokens state out raw : Term ctx) : Formula ctx :=
 property ptag atag ltag rtag ttag prefixCode (HistoryKernel.pairCall ptag tokens (HistoryKernel.pairCall ptag state out)) raw
theorem substProperty {m n : Nat} (s : Fin m → Term n) ptag atag ltag rtag ttag (prefixCode packed raw : Term m) :
 substituteFormula s (property ptag atag ltag rtag ttag prefixCode packed raw) =
 property ptag atag ltag rtag ttag (substitute s prefixCode) (substitute s packed) (substitute s raw) := by
 simp only [property,UniformSubstitutionErasure.newTickCall,substituteFormula,substTransformed,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil]
theorem substPacked {m n : Nat} (s : Fin m → Term n) ptag atag ltag rtag ttag (prefixCode tokens state out raw : Term m) :
 substituteFormula s (packedProperty ptag atag ltag rtag ttag prefixCode tokens state out raw) =
 packedProperty ptag atag ltag rtag ttag (substitute s prefixCode) (substitute s tokens) (substitute s state) (substitute s out) (substitute s raw) := by
 simp only [packedProperty,substProperty,HistoryKernel.pairCall,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil]
theorem weakenPacked {ctx : Nat} ptag atag ltag rtag ttag (prefixCode tokens state out raw : Term ctx) :
 GorbowPACore.weaken (packedProperty ptag atag ltag rtag ttag prefixCode tokens state out raw) =
 packedProperty ptag atag ltag rtag ttag (liftTerm prefixCode) (liftTerm tokens) (liftTerm state) (liftTerm out) (liftTerm raw) := by
 rw [GorbowPACore.weaken,substPacked]
 rfl
noncomputable def transport {T : Sentence → Prop} {ctx : Nat} ptag atag ltag rtag ttag (prefixCode a b raw : Term ctx) :
 Derivation T (.imp (.equal a b)
  (.imp (property ptag atag ltag rtag ttag prefixCode a raw) (property ptag atag ltag rtag ttag prefixCode b raw))) := by
 have h := Derivation.logical (A := T) (.equalityReplace
  (property ptag atag ltag rtag ttag (liftTerm prefixCode) (.var 0) (liftTerm raw)) a b)
 simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substProperty,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using h
noncomputable def transportPacked {T : Sentence → Prop} {ctx : Nat} ptag atag ltag rtag ttag (prefixCode a b state out raw : Term ctx) :
 Derivation T (.imp (.equal a b)
  (.imp (packedProperty ptag atag ltag rtag ttag prefixCode a state out raw)
   (packedProperty ptag atag ltag rtag ttag prefixCode b state out raw))) := by
 have h := Derivation.logical (A := T) (.equalityReplace
  (packedProperty ptag atag ltag rtag ttag (liftTerm prefixCode) (.var 0) (liftTerm state) (liftTerm out) (liftTerm raw)) a b)
 simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substPacked,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using h
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNegatedInstanceBridge.InlineFrame.LogicProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNegatedInstanceBridge.InlineFrame.LogicProof
