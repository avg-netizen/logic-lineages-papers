module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.IterationEquationsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.IterationFirstProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport Iteration IterationEquationsProof

def first {ctx : Nat} (tag : Nat) (count state : Term ctx) : Formula ctx :=
 .equal (runCall tag (.succ count) state)
  (runCall tag count (call (tickTag tag) (state ::ᵥ nil)))
theorem substFirst {m n : Nat} (sub : Fin m → Term n) tag (count state : Term m) :
 substituteFormula sub (first tag count state) = first tag (substitute sub count) (substitute sub state) := by
 simp only [first,substituteFormula,substRun,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,substitute]

theorem base {n ctx : Nat} (p : Program n) tag
 (ht : (nodes p)[tag]? = some ⟨2,iterator⟩) (state : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (first tag .zero state)) := by
 obtain ⟨hs⟩ := IterationEquationsProof.successor p tag ht .zero state
 obtain ⟨hz⟩ := IterationEquationsProof.zero p tag ht state
 obtain ⟨hr⟩ := IterationEquationsProof.zero p tag ht (call (tickTag tag) (state ::ᵥ nil))
 have hmid := HistoryLookup.DestructorProof.unaryCallCongruence (tickTag tag) _ _ hz
 exact ⟨Logic.trans _ _ _ hs (Logic.trans _ _ _ hmid (Support.equalitySymmetry _ _ hr))⟩

theorem step {n ctx : Nat} (p : Program n) tag
 (ht : (nodes p)[tag]? = some ⟨2,iterator⟩) (count state : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (first tag count state) (first tag (.succ count) state))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := first tag count state
 have hh : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
 obtain ⟨hl⟩ := IterationEquationsProof.successor p tag ht (.succ count) state
 obtain ⟨hr⟩ := IterationEquationsProof.successor p tag ht count (call (tickTag tag) (state ::ᵥ nil))
 have hm := localUnary (call (tickTag tag) (.var 0 ::ᵥ nil))
  (runCall tag (.succ count) state)
  (runCall tag count (call (tickTag tag) (state ::ᵥ nil))) hh
 simp only [Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,substitute,Fin.cases_zero] at hm
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge
  (localTrans _ _ _ (.base hl) (localTrans _ _ _ hm (.base (Support.equalitySymmetry _ _ hr)))))⟩

theorem internalFirst {n ctx : Nat} (p : Program n) tag
 (ht : (nodes p)[tag]? = some ⟨2,iterator⟩) (count state : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (first tag count state)) := by
 let phi : Formula (ctx+1) := first tag (.var 0) (liftTerm state)
 obtain ⟨hz⟩ := base p tag ht state
 have hb : Derivation (GorbowPRNumeralCalculation.Theory p)
  (GorbowStandardInstances.instantiate phi .zero) := by
  simpa only [phi,GorbowStandardInstances.instantiate,substFirst,substitute,
   liftTerm,Support.shiftCancel,Fin.cases_zero] using hz
 obtain ⟨hs0⟩ := step p tag ht (.var 0 : Term (ctx+1)) (liftTerm state)
 have hs : Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp phi (GorbowStandardInduction.successorInstance phi)) := by
  simpa only [phi,GorbowStandardInduction.successorInstance,substFirst,substitute,
   successorLift,Fin.cases_zero,Support.shiftCancel] using hs0
 have h := atTerm phi count (induction phi hb hs)
 exact ⟨by simpa only [phi,GorbowStandardInstances.instantiate,substFirst,substitute,
  liftTerm,Support.shiftCancel,Fin.cases_zero] using h⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.IterationFirstProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.IterationFirstProof
