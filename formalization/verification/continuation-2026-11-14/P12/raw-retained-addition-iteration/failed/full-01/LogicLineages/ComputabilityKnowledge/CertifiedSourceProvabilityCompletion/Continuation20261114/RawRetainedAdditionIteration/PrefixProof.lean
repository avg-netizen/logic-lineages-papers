module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedAdditionIteration.IterationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedAdditionIteration.PrefixProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof List.Vector SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open GorbowSubstitution GorbowFormulaSubstitution
def template {ctx : Nat} (pref num : Nat) (m : Term ctx) : Formula (ctx+1) :=
 .equal (RawRetainedAdditionIteration.binaryCall pref (.var 0) (LiteralNumeralPrefix.numeralCall num (liftTerm m)))
  (LiteralNumeralPrefix.numeralCall num (.add (liftTerm m) (.var 0)))
theorem templateAt {ctx : Nat} pref num (m k : Term ctx) :
 GorbowStandardInstances.instantiate (template pref num m) k =
 .equal (RawRetainedAdditionIteration.binaryCall pref k (LiteralNumeralPrefix.numeralCall num m))
  (LiteralNumeralPrefix.numeralCall num (.add m k)) := by
 simp only [GorbowStandardInstances.instantiate,template,substituteFormula,RawRetainedAdditionIteration.binaryCall,
  LiteralNumeralPrefix.numeralCall,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,
  substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

theorem internalPrefixNumeral : ∀ n (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x), ∀ ctx (m k : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (binaryCall I.prefixTag k (LiteralNumeralPrefix.numeralCall I.numeralTag m))
   (LiteralNumeralPrefix.numeralCall I.numeralTag (.add m k)))) := by
 intro n p old a x I ctx m k
 let T := GorbowPRNumeralCalculation.Theory p
 let phi := template I.prefixTag I.numeralTag m
 obtain ⟨hpz⟩ := RawRetainedAdditionIteration.EquationsProof.prefixZero p old a x I (LiteralNumeralPrefix.numeralCall I.numeralTag m)
 have haz : Derivation T (.equal (.add m .zero) m) := .arithmetic (.addZero m)
 have hnz := HistoryLookup.DestructorProof.unaryCallCongruence I.numeralTag _ _ haz
 have hb : Derivation T (GorbowStandardInstances.instantiate phi .zero) := by
  simpa only [phi,templateAt,LiteralNumeralPrefix.numeralCall,T] using Logic.trans _ _ _ hpz (Support.equalitySymmetry _ _ hnz)
 let M := liftTerm m
 let j : Term (ctx+1) := .var 0
 have hih : Hilbert.Local T (ctx+1) [phi] phi := .hypothesis List.mem_cons_self
 obtain ⟨hps⟩ := RawRetainedAdditionIteration.EquationsProof.prefixSuccessor p old a x I j (LiteralNumeralPrefix.numeralCall I.numeralTag M)
 have hcons := HistoryIteratorSuffix.StepSuffixProof.pairCongruence (T := T) (G := [phi]) I.ctag
  (Term.numeral 2) _ (Term.numeral 2) _ (.base (.logical (.reflexive _))) hih
 obtain ⟨hns⟩ := LiteralNumeralPrefix.EquationsProof.successor p I.numeralTag I.ctag I.hnumeral I.hc (.add M j)
 have has : Derivation T (.equal (.add M (.succ j)) (.succ (.add M j))) := .arithmetic (.addSucc M j)
 have hnc := HistoryLookup.DestructorProof.unaryCallCongruence I.numeralTag _ _ has
 have hout := localTrans _ _ _ (.base hps) (localTrans _ _ _ hcons
  (.base (Logic.trans _ _ _ (Support.equalitySymmetry _ _ hns) (Support.equalitySymmetry _ _ hnc))))
 have hs : Derivation T (.imp phi (GorbowStandardInduction.successorInstance phi)) := by
  simpa only [phi,template,GorbowStandardInduction.successorInstance,substituteFormula,
   RawRetainedAdditionIteration.binaryCall,LiteralNumeralPrefix.numeralCall,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,
   substitute,successorLift,Fin.cases_zero,M,j] using Hilbert.Local.finish (Hilbert.Local.discharge hout)
 have h := atTerm phi k (HistoryCodec.ArithmeticSupport.induction phi hb hs)
 exact ⟨by simpa only [phi,templateAt,T] using h⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedAdditionIteration.PrefixProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedAdditionIteration.PrefixProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedAdditionIteration.PrefixProof.internalPrefixNumeral
