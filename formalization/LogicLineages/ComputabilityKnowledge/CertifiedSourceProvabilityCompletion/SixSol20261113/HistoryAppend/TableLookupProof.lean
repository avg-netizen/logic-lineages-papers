module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryAppend.TableEquationsProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryAppend.TableLookupProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport TableEquationsProof

def headCall {ctx : Nat} (htag : Nat) (code : Term ctx) : Term ctx := call htag (code ::ᵥ nil)

theorem substHead {m n : Nat} (sub : Fin m → Term n) htag (code : Term m) :
    substitute sub (headCall htag code) = headCall htag (substitute sub code) := by
  simp only [headCall,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil]
theorem substLookup {m n : Nat} (sub : Fin m → Term n) ltag (index code : Term m) :
    substitute sub (HistoryLookup.lookupCall ltag index code) =
      HistoryLookup.lookupCall ltag (substitute sub index) (substitute sub code) := by
  simp only [HistoryLookup.lookupCall,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil]

noncomputable def lookupCodeCongruence {T : Sentence → Prop} {ctx : Nat} ltag (index s t : Term ctx)
    (h : Derivation T (.equal s t)) :
    Derivation T (.equal (HistoryLookup.lookupCall ltag index s) (HistoryLookup.lookupCall ltag index t)) := by
  have d := Logic.unary (HistoryLookup.lookupCall ltag (liftTerm index) (.var 0)) s t h
  simpa only [substLookup,liftTerm,Support.shiftCancel,substitute,Fin.cases_zero] using d

theorem zeroAtCons {n ctx : Nat} (p : Program n) ltag htag ctag
    (hl : (nodes p)[ltag]? = some ⟨2,HistoryLookup.lookup⟩)
    (hh : (nodes p)[htag]? = some ⟨1,HistoryLookup.head⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (code a b : Term ctx)
    (he : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal code (HistoryLookup.consCall ctag a b))) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (HistoryLookup.lookupCall ltag .zero code) (.succ (headCall htag code)))) := by
  obtain ⟨hlookup⟩ := HistoryLookup.LookupProof.internalLookupZeroCons n p ltag ctag hl hc ctx a b
  obtain ⟨hhead⟩ := HistoryLookup.DestructorProof.internalHeadCons n p htag ctag hh hc ctx a b
  have hlc := Logic.trans _ _ _ (lookupCodeCongruence ltag .zero _ _ he) hlookup
  have hhc := Logic.trans _ _ _ (HistoryLookup.DestructorProof.unaryCallCongruence htag _ _ he) hhead
  exact ⟨Logic.trans _ _ _ hlc (Support.equalitySymmetry _ _ (Logic.unary (.succ (.var 0)) _ _ hhc))⟩

def zeroTemplate {ctx : Nat} (tag ltag htag : Nat) (right : Term ctx) : Formula (ctx+1) :=
  .equal (HistoryLookup.lookupCall ltag .zero (tableCall tag (.var 0) (liftTerm right)))
    (.succ (headCall htag (tableCall tag (.var 0) (liftTerm right))))

theorem zeroAt {ctx : Nat} tag ltag htag (right count : Term ctx) :
    GorbowStandardInstances.instantiate (zeroTemplate tag ltag htag right) count =
      .equal (HistoryLookup.lookupCall ltag .zero (tableCall tag count right))
        (.succ (headCall htag (tableCall tag count right))) := by
  simp only [GorbowStandardInstances.instantiate,zeroTemplate,substituteFormula,substLookup,substHead,substTable,
    substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

theorem tableLookupZero {n ctx : Nat} (p : Program n) tag ltag htag
    (ht : (nodes p)[tag]? = some ⟨2,table⟩)
    (hl : (nodes p)[ltag]? = some ⟨2,HistoryLookup.lookup⟩)
    (hh : (nodes p)[htag]? = some ⟨1,HistoryLookup.head⟩) (count right : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (HistoryLookup.lookupCall ltag .zero (tableCall tag count right))
        (.succ (headCall htag (tableCall tag count right))))) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let phi := zeroTemplate tag ltag htag right
  have hc := consInstalled p tag ht
  obtain ⟨hz⟩ := tableZero p tag ht right
  obtain ⟨hbase⟩ := zeroAtCons p ltag htag (consTag tag) hl hh hc _ right .zero hz
  have hb : Derivation T (GorbowStandardInstances.instantiate phi .zero) := by
    rw [show phi = zeroTemplate tag ltag htag right from rfl,zeroAt]
    exact hbase
  let x : Term (ctx+1) := .var 0
  let R := liftTerm right
  obtain ⟨hstep⟩ := tableSuccessor p tag ht x R
  obtain ⟨hresult⟩ := zeroAtCons p ltag htag (consTag tag) hl hh hc _
    (entryCall tag x (tableCall tag x R) R) (tableCall tag x R) hstep
  have hs : Derivation T (.imp phi (GorbowStandardInduction.successorInstance phi)) := by
    simp only [phi,zeroTemplate,GorbowStandardInduction.successorInstance,substituteFormula,
      substLookup,substHead,substTable,substitute,successorLift,Fin.cases_zero]
    exact Hilbert.lift _ hresult
  have h := atTerm phi count (HistoryCodec.ArithmeticSupport.induction phi hb hs)
  rw [show phi = zeroTemplate tag ltag htag right from rfl,zeroAt] at h
  exact ⟨h⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryAppend.TableLookupProof
