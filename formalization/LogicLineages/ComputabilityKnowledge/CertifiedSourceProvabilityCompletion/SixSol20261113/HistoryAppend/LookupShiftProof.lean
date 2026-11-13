module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryAppend.ConsProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRInternalCoherenceProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryAppend.LookupShiftProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open HistoryLookup.DropEquationsProof

def template {ctx : Nat} (tag : Nat) (code : Term ctx) : Formula (ctx+1) :=
  .equal (dropCall tag (.succ (.var 0)) (liftTerm code))
    (dropCall tag (.var 0) (call (tailTag tag) (liftTerm code ::ᵥ nil)))

theorem templateAt {ctx : Nat} tag (code index : Term ctx) :
    GorbowStandardInstances.instantiate (template tag code) index =
      .equal (dropCall tag (.succ index) code) (dropCall tag index (call (tailTag tag) (code ::ᵥ nil))) := by
  simp only [GorbowStandardInstances.instantiate,template,substituteFormula,substDrop,Logic.substCall,
    List.Vector.map_cons,List.Vector.map_nil,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

theorem dropShift {n ctx : Nat} (p : Program n) tag (ht : (nodes p)[tag]? = some ⟨2,HistoryLookup.drop⟩) (index code : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (dropCall tag (.succ index) code) (dropCall tag index (call (tailTag tag) (code ::ᵥ nil))))) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let phi := template tag code
  obtain ⟨hzs⟩ := dropSuccessor p tag ht .zero code
  obtain ⟨hzc⟩ := dropZero p tag ht code
  obtain ⟨hzt⟩ := dropZero p tag ht (call (tailTag tag) (code ::ᵥ nil))
  have hb : Derivation T (GorbowStandardInstances.instantiate phi .zero) := by
    rw [show phi = template tag code from rfl,templateAt]
    exact Logic.trans _ _ _ hzs (Logic.trans _ _ _
      (HistoryLookup.DestructorProof.unaryCallCongruence (tailTag tag) _ _ hzc) (Support.equalitySymmetry _ _ hzt))
  let C := liftTerm code
  let x : Term (ctx+1) := .var 0
  have hi : Hilbert.Local T (ctx+1) [phi]
      (.equal (dropCall tag (.succ x) C) (dropCall tag x (call (tailTag tag) (C ::ᵥ nil)))) := .hypothesis List.mem_cons_self
  obtain ⟨hl⟩ := dropSuccessor p tag ht (.succ x) C
  obtain ⟨hr⟩ := dropSuccessor p tag ht x (call (tailTag tag) (C ::ᵥ nil))
  have hc := localUnary (call (tailTag tag) (.var 0 ::ᵥ nil)) _ _ hi
  simp only [Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,substitute,Fin.cases_zero] at hc
  have hout := localTrans _ _ _ (.base hl) (localTrans _ _ _ hc (.base (Support.equalitySymmetry _ _ hr)))
  have hs : Derivation T (.imp phi (GorbowStandardInduction.successorInstance phi)) := by
    simp only [phi,template,GorbowStandardInduction.successorInstance,substituteFormula,substDrop,
      Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,substitute,successorLift,Fin.cases_zero]
    exact Hilbert.Local.finish (Hilbert.Local.discharge hout)
  have h := atTerm phi index (HistoryCodec.ArithmeticSupport.induction phi hb hs)
  rw [show phi = template tag code from rfl,templateAt] at h
  exact ⟨h⟩

/-- Arbitrary code shift, transported to any installed copy of the actual tail. -/
theorem lookupShift {n ctx : Nat} (p : Program n) tag ttag
    (ht : (nodes p)[tag]? = some ⟨2,HistoryLookup.lookup⟩)
    (htt : (nodes p)[ttag]? = some ⟨1,HistoryLookup.tail⟩) (index code : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (HistoryLookup.lookupCall tag (.succ index) code)
        (HistoryLookup.lookupCall tag index (call ttag (code ::ᵥ nil))))) := by
  let dt := HistoryLookup.LookupProof.dropTag tag
  have hd := SixSol20261112.Fuel.Equations.argumentChild p tag HistoryLookup.reference (fun _ : Fin 1 => HistoryLookup.drop) ht 0
  obtain ⟨hl⟩ := HistoryLookup.LookupProof.lookupEquation p tag ht (.succ index) code
  obtain ⟨hr⟩ := HistoryLookup.LookupProof.lookupEquation p tag ht index (call (tailTag dt) (code ::ᵥ nil))
  obtain ⟨hs⟩ := dropShift p dt hd index code
  have h := Logic.trans _ _ _ hl (Logic.trans _ _ _
    (HistoryLookup.DestructorProof.unaryCallCongruence (tag+1) _ _ hs) (Support.equalitySymmetry _ _ hr))
  obtain ⟨hcopy⟩ := GorbowPRInternalCoherence.Proof.registryCoherence n p (tailTag dt) ttag 1 HistoryLookup.tail
    (tailInstalled p dt hd) htt ctx (code ::ᵥ nil)
  exact ⟨Logic.trans _ _ _ h (PositiveProof.binaryCongruence tag index index _ _ (.logical (.reflexive index)) hcopy)⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryAppend.LookupShiftProof
