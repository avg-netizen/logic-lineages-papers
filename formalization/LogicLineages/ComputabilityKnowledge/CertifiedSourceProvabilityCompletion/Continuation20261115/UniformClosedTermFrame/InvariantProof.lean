module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.EntriesLogic
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.InvariantProof
open GorbowSyntax GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph
/-- The old pending stack consists only of original term tasks at bound zero.
A depth-related arbitrary prefix is placed over an unchanged arbitrary rest.
All three antecedents are internally discharged at the public singleton input. -/
def property {ctx : Nat} (ftag stag ptag ctag atag len q l r : Nat)
 (tokens raw oldTasks newTasks rest out : Term ctx) : Formula ctx :=
 .imp (EntriesLogic.entries q (LiteralSyntaxStep.taskCall ptag 0 .zero) oldTasks)
  (.imp (RelationalSyntaxDepthTransport.stackRelation len q l r oldTasks newTasks)
   (.imp (.equal (LiteralSyntaxScan.scanCall stag oldTasks tokens) (.succ .zero))
    (.equal (UniformClosedSubstitutionRawFold.foldCall ftag tokens
     (HistoryKernel.pairCall ptag (.succ (HistoryAppend.appendCall atag newTasks rest)) out) raw)
     (final ptag atag rest out tokens))))
theorem substProperty {m n : Nat} (s : Fin m → Term n) ftag stag ptag ctag atag len q l r
 (tokens raw oldTasks newTasks rest out : Term m) :
 substituteFormula s (property ftag stag ptag ctag atag len q l r tokens raw oldTasks newTasks rest out) =
 property ftag stag ptag ctag atag len q l r (substitute s tokens) (substitute s raw)
  (substitute s oldTasks) (substitute s newTasks) (substitute s rest) (substitute s out) := by
 simp only [property,substituteFormula,EntriesLogic.substEntries,
  RelationalSyntaxDepthTransport.SubstitutionProof.substStack,LiteralSyntaxStep.taskCall,
  UniformClosedSubstitutionRawFold.foldCall,LiteralSyntaxScan.scanCall,final,
  HistoryKernel.pairCall,HistoryAppend.PreserveSupportProof.substAppend,
  Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,
  LiteralSyntaxStep.ExpansionSupportProof.substituteNumeral,substitute]
theorem weakenProperty {ctx : Nat} ftag stag ptag ctag atag len q l r
 (tokens raw oldTasks newTasks rest out : Term ctx) :
 GorbowPACore.weaken (property ftag stag ptag ctag atag len q l r tokens raw oldTasks newTasks rest out) =
 property ftag stag ptag ctag atag len q l r (liftTerm tokens) (liftTerm raw)
  (liftTerm oldTasks) (liftTerm newTasks) (liftTerm rest) (liftTerm out) := by
 rw [GorbowPACore.weaken,substProperty]
 rfl
noncomputable def transportTokens {T : Sentence → Prop} {ctx : Nat} ftag stag ptag ctag atag len q l r
 (a b raw oldTasks newTasks rest out : Term ctx) :
 Derivation T (.imp (.equal a b)
  (.imp (property ftag stag ptag ctag atag len q l r a raw oldTasks newTasks rest out)
   (property ftag stag ptag ctag atag len q l r b raw oldTasks newTasks rest out))) := by
 have h := Derivation.logical (A := T) (.equalityReplace
  (property ftag stag ptag ctag atag len q l r (.var 0) (liftTerm raw) (liftTerm oldTasks)
   (liftTerm newTasks) (liftTerm rest) (liftTerm out)) a b)
 simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substProperty,
  substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using h
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.InvariantProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.InvariantProof
