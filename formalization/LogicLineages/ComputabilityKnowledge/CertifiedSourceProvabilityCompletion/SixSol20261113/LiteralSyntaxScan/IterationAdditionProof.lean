module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.IterationEquationsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.IterationAdditionProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport Iteration IterationEquationsProof

def addition {ctx : Nat} (tag : Nat) (a b state : Term ctx) : Formula ctx :=
 .equal (runCall tag (.add a b) state) (runCall tag b (runCall tag a state))
theorem substAddition {m n : Nat} (sub : Fin m → Term n) tag (a b state : Term m) :
 substituteFormula sub (addition tag a b state) =
 addition tag (substitute sub a) (substitute sub b) (substitute sub state) := by
 simp only [addition,substituteFormula,substRun,substitute]

theorem base {n ctx : Nat} (p : Program n) tag
 (ht : (nodes p)[tag]? = some ⟨2,iterator⟩) (a state : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (addition tag a .zero state)) := by
 obtain ⟨hz⟩ := IterationEquationsProof.zero p tag ht (runCall tag a state)
 have hleft := HistoryAppend.PositiveProof.binaryCongruence tag (.add a .zero) a state state
  (.arithmetic (.addZero a)) (.logical (.reflexive state))
 exact ⟨Logic.trans _ _ _ hleft (Support.equalitySymmetry _ _ hz)⟩

theorem step {n ctx : Nat} (p : Program n) tag
 (ht : (nodes p)[tag]? = some ⟨2,iterator⟩) (a b state : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (addition tag a b state) (addition tag a (.succ b) state))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := addition tag a b state
 have hh : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
 have hleft := HistoryAppend.PositiveProof.binaryCongruence tag (.add a (.succ b))
  (.succ (.add a b)) state state (.arithmetic (.addSucc a b)) (.logical (.reflexive state))
 obtain ⟨hl⟩ := IterationEquationsProof.successor p tag ht (.add a b) state
 obtain ⟨hr⟩ := IterationEquationsProof.successor p tag ht b (runCall tag a state)
 have hm := localUnary (call (tickTag tag) (.var 0 ::ᵥ nil))
  (runCall tag (.add a b) state) (runCall tag b (runCall tag a state)) hh
 simp only [Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,substitute,Fin.cases_zero] at hm
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge
  (localTrans _ _ _ (.base (Logic.trans _ _ _ hleft hl))
   (localTrans _ _ _ hm (.base (Support.equalitySymmetry _ _ hr)))))⟩

theorem internalAddition : IterationTargets.InternalAddition := by
 intro n p tag ht ctx a b state
 let phi : Formula (ctx+1) := addition tag (liftTerm a) (.var 0) (liftTerm state)
 obtain ⟨hz⟩ := base p tag ht a state
 have hb : Derivation (GorbowPRNumeralCalculation.Theory p)
  (GorbowStandardInstances.instantiate phi .zero) := by
  simpa only [phi,GorbowStandardInstances.instantiate,substAddition,substitute,
   liftTerm,Support.shiftCancel,Fin.cases_zero] using hz
 obtain ⟨hs0⟩ := step p tag ht (liftTerm a) (.var 0 : Term (ctx+1)) (liftTerm state)
 have hs : Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp phi (GorbowStandardInduction.successorInstance phi)) := by
  simpa only [phi,GorbowStandardInduction.successorInstance,substAddition,substitute,
   successorLift,Fin.cases_zero,Support.shiftCancel] using hs0
 have h := atTerm phi b (induction phi hb hs)
 exact ⟨by simpa only [phi,GorbowStandardInstances.instantiate,substAddition,substitute,
  liftTerm,Support.shiftCancel,Fin.cases_zero] using h⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.IterationAdditionProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.IterationAdditionProof
