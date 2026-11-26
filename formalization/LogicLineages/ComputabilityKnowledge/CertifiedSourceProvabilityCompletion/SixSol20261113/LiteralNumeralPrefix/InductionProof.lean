module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralNumeralPrefix.Targets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.IterationFirstProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralNumeralPrefix.InductionProof
open GorbowSyntax GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport

def property {ctx : Nat} (ntag stag ptag ctag : Nat) (value binder rest : Term ctx) : Formula ctx :=
 .equal (LiteralSyntaxScan.scanCall stag
  (HistoryLookup.consCall ctag (termTask ptag binder) rest) (numeralCall ntag value)) (.succ rest)
theorem substProperty {m n : Nat} (sub : Fin m → Term n) ntag stag ptag ctag (value binder rest : Term m) :
 substituteFormula sub (property ntag stag ptag ctag value binder rest) =
 property ntag stag ptag ctag (substitute sub value) (substitute sub binder) (substitute sub rest) := by
 simp only [property,LiteralSyntaxScan.scanCall,HistoryLookup.consCall,termTask,LiteralSyntaxStep.taskCall,
  HistoryKernel.pairCall,numeralCall,substituteFormula,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,
  substitute,Logic.substNumeral]

theorem fromBaseStep {T : Sentence → Prop} {ctx : Nat} ntag stag ptag ctag
 (value binder rest : Term ctx)
 (hz : Derivation T (property ntag stag ptag ctag .zero binder rest))
 (hs0 : Derivation T (.imp
  (property ntag stag ptag ctag (.var 0 : Term (ctx+1)) (liftTerm binder) (liftTerm rest))
  (property ntag stag ptag ctag (.succ (.var 0)) (liftTerm binder) (liftTerm rest)))) :
 Nonempty (Derivation T (property ntag stag ptag ctag value binder rest)) := by
 let phi : Formula (ctx+1) := property ntag stag ptag ctag (.var 0) (liftTerm binder) (liftTerm rest)
 have hb : Derivation T (GorbowStandardInstances.instantiate phi .zero) := by
  simpa only [phi,GorbowStandardInstances.instantiate,substProperty,substitute,
   liftTerm,Support.shiftCancel,Fin.cases_zero] using hz
 have hs : Derivation T (.imp phi (GorbowStandardInduction.successorInstance phi)) := by
  simpa only [phi,GorbowStandardInduction.successorInstance,substProperty,substitute,
   successorLift,Fin.cases_zero,Support.shiftCancel] using hs0
 have h := atTerm phi value (induction phi hb hs)
 exact ⟨by simpa only [phi,GorbowStandardInstances.instantiate,substProperty,substitute,
  liftTerm,Support.shiftCancel,Fin.cases_zero] using h⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralNumeralPrefix.InductionProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralNumeralPrefix.InductionProof
