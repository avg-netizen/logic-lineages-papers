module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionErasure.TickProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionErasure.IterationProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open UniformClosedSubstitutionFold (iterateCall)
open LiteralSyntaxScan.Iteration (runCall)
open HistoryLookup.DestructorProof (unaryCallCongruence)
def property {ctx : Nat} (etag ntag otag : Nat) (count state raw : Term ctx) : Formula ctx :=
 .equal (eraseCall etag (iterateCall ntag count state raw)) (runCall otag count (eraseCall etag state))
theorem substProperty {m n : Nat} (s : Fin m → Term n) etag ntag otag (count state raw : Term m) :
 substituteFormula s (property etag ntag otag count state raw) =
 property etag ntag otag (substitute s count) (substitute s state) (substitute s raw) := by
 simp only [property,eraseCall,iterateCall,runCall,substituteFormula,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil]
theorem base {n ctx : Nat} (p : Program n) (etag ntag otag : Nat)
 (hn : (nodes p)[ntag]? = some ⟨3,UniformClosedSubstitutionFold.iterator⟩)
 (ho : (nodes p)[otag]? = some ⟨2,LiteralSyntaxScan.iterator⟩) (state raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (property etag ntag otag .zero state raw)) := by
 obtain ⟨hnew⟩ := UniformClosedSubstitutionFold.IterationProof.zero p ntag hn state raw
 obtain ⟨hold⟩ := LiteralSyntaxScan.IterationEquationsProof.zero p otag ho (eraseCall etag state)
 exact ⟨Logic.trans _ _ _ (unaryCallCongruence etag _ _ hnew) (Support.equalitySymmetry _ _ hold)⟩
theorem step {n ctx : Nat} (p : Program n) (etag ntag otag : Nat)
 (he : (nodes p)[etag]? = some ⟨1,eraseCode⟩)
 (hn : (nodes p)[ntag]? = some ⟨3,UniformClosedSubstitutionFold.iterator⟩)
 (ho : (nodes p)[otag]? = some ⟨2,LiteralSyntaxScan.iterator⟩) (count state raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (property etag ntag otag count state raw) (property etag ntag otag (.succ count) state raw))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := property etag ntag otag count state raw
 have hh : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
 obtain ⟨hnew⟩ := UniformClosedSubstitutionFold.IterationProof.successor p ntag hn count state raw
 obtain ⟨hold⟩ := LiteralSyntaxScan.IterationEquationsProof.successor p otag ho count (eraseCall etag state)
 obtain ⟨htick⟩ := TickProof.exactTick n p etag
  (UniformClosedSubstitutionFold.IterationProof.tickTag ntag) (LiteralSyntaxScan.IterationEquationsProof.tickTag otag)
  he (UniformClosedSubstitutionFold.IterationProof.tickInstalled p ntag hn)
  (LiteralSyntaxScan.IterationEquationsProof.tickInstalled p otag ho) ctx (iterateCall ntag count state raw) raw
 have hm := localUnary (call (LiteralSyntaxScan.IterationEquationsProof.tickTag otag) (.var 0 ::ᵥ nil))
  (eraseCall etag (iterateCall ntag count state raw)) (runCall otag count (eraseCall etag state)) hh
 simp only [Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,substitute,Fin.cases_zero] at hm
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge
  (localTrans _ _ _ (.base (unaryCallCongruence etag _ _ hnew))
   (localTrans _ _ _ (.base htick) (localTrans _ _ _ hm (.base (Support.equalitySymmetry _ _ hold))))))⟩
theorem exactIterator : Targets.InternalIteratorErasure := by
 intro n p etag ntag otag he hn ho ctx count state raw
 let phi : Formula (ctx+1) := property etag ntag otag (.var 0) (liftTerm state) (liftTerm raw)
 obtain ⟨hz⟩ := base p etag ntag otag hn ho state raw
 have hb : Derivation (GorbowPRNumeralCalculation.Theory p) (GorbowStandardInstances.instantiate phi .zero) := by
  simpa only [phi,GorbowStandardInstances.instantiate,substProperty,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using hz
 obtain ⟨hs0⟩ := step p etag ntag otag he hn ho (.var 0 : Term (ctx+1)) (liftTerm state) (liftTerm raw)
 have hs : Derivation (GorbowPRNumeralCalculation.Theory p) (.imp phi (GorbowStandardInduction.successorInstance phi)) := by
  simpa only [phi,GorbowStandardInduction.successorInstance,substProperty,substitute,successorLift,Fin.cases_zero,Support.shiftCancel] using hs0
 have h := atTerm phi count (induction phi hb hs)
 change Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (property etag ntag otag count state raw))
 exact ⟨by simpa only [phi,GorbowStandardInstances.instantiate,substProperty,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using h⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionErasure.IterationProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionErasure.IterationProof
