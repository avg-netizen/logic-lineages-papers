module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalStateRetention.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalStateRetention.TransportProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport HistoryKernel
open HistoryIteratorSuffix HistoryIteratorSuffix.WitnessProof HistoryIteratorSuffix.StepSuffixProof

theorem substPreserves {m n : Nat} (s : Fin m → Term n) ot nt ptag (state index fuel out rest : Term m) :
 substituteFormula s (preserves ot nt ptag state index fuel out rest) =
 preserves ot nt ptag (substitute s state) (substitute s index) (substitute s fuel) (substitute s out) (substitute s rest) := by
 simp only [preserves,substituteFormula,kernelCall,substPair,Logic.substCall,map_cons,map_nil,substitute]
theorem weakenPreserves {ctx : Nat} ot nt ptag (state index fuel out rest : Term ctx) :
 GorbowPACore.weaken (preserves ot nt ptag state index fuel out rest) =
 preserves ot nt ptag (liftTerm state) (liftTerm index) (liftTerm fuel) (liftTerm out) (liftTerm rest) := by
 rw [GorbowPACore.weaken,substPreserves]
 rfl
noncomputable def moveState {T : Sentence → Prop} {ctx : Nat} ot nt ptag
 (a b index fuel out rest : Term ctx) : Derivation T
 (.imp (.equal a b) (.imp (preserves ot nt ptag a index fuel out rest) (preserves ot nt ptag b index fuel out rest))) := by
 have he := Derivation.logical (A := T) (.equalityReplace
  (preserves ot nt ptag (.var 0) (liftTerm index) (liftTerm fuel) (liftTerm out) (liftTerm rest)) a b)
 simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substPreserves,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using he
noncomputable def moveLines {T : Sentence → Prop} {ctx : Nat} ot nt ptag
 (h a b index fuel out rest : Term ctx) : Derivation T
 (.imp (.equal a b) (.imp (preserves ot nt ptag (pairCall ptag (.succ h) a) index fuel out rest)
 (preserves ot nt ptag (pairCall ptag (.succ h) b) index fuel out rest))) := by
 have he := Derivation.logical (A := T) (.equalityReplace
  (preserves ot nt ptag (pairCall ptag (.succ (liftTerm h)) (.var 0)) (liftTerm index) (liftTerm fuel) (liftTerm out) (liftTerm rest)) a b)
 simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substPreserves,substPair,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using he

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalStateRetention.TransportProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalStateRetention.TransportProof
