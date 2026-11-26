module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLookup.DropEquationsProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLookup.DropProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport DropEquationsProof

def consTemplate {ctx : Nat} (tag ctag : Nat) (a b : Term ctx) : Formula (ctx+1) :=
  .equal (dropCall tag (.succ (.var 0)) (consCall ctag (liftTerm a) (liftTerm b)))
    (dropCall tag (.var 0) (liftTerm b))

theorem consAt {ctx : Nat} tag ctag (a b index : Term ctx) :
    GorbowStandardInstances.instantiate (consTemplate tag ctag a b) index =
      .equal (dropCall tag (.succ index) (consCall ctag a b)) (dropCall tag index b) := by
  simp only [GorbowStandardInstances.instantiate,consTemplate,substituteFormula,substDrop,substCons,
    substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

theorem dropCons {n ctx : Nat} (p : Program n) tag ctag
    (ht : (nodes p)[tag]? = some ⟨2,drop⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (index a b : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (dropCall tag (.succ index) (consCall ctag a b)) (dropCall tag index b))) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let phi := consTemplate tag ctag a b
  have htail := tailInstalled p tag ht
  obtain ⟨hzs⟩ := dropSuccessor p tag ht .zero (consCall ctag a b)
  obtain ⟨hzc⟩ := dropZero p tag ht (consCall ctag a b)
  obtain ⟨hzt⟩ := DestructorProof.internalTailCons n p (tailTag tag) ctag htail hc ctx a b
  obtain ⟨hzb⟩ := dropZero p tag ht b
  have hb : Derivation T (GorbowStandardInstances.instantiate phi .zero) := by
    rw [show phi = consTemplate tag ctag a b from rfl,consAt]
    exact Logic.trans _ _ _ hzs (Logic.trans _ _ _
      (DestructorProof.unaryCallCongruence (tailTag tag) _ _ hzc)
      (Logic.trans _ _ _ hzt (Support.equalitySymmetry _ _ hzb)))
  let A := liftTerm a
  let B := liftTerm b
  let x : Term (ctx+1) := .var 0
  have hi : Hilbert.Local T (ctx+1) [phi]
      (.equal (dropCall tag (.succ x) (consCall ctag A B)) (dropCall tag x B)) := .hypothesis List.mem_cons_self
  obtain ⟨hl⟩ := dropSuccessor p tag ht (.succ x) (consCall ctag A B)
  obtain ⟨hr⟩ := dropSuccessor p tag ht x B
  have hcong := localUnary (call (tailTag tag) (.var 0 ::ᵥ nil)) _ _ hi
  simp only [Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,substitute,Fin.cases_zero] at hcong
  have hout := localTrans _ _ _ (.base hl) (localTrans _ _ _ hcong (.base (Support.equalitySymmetry _ _ hr)))
  have hs : Derivation T (.imp phi (GorbowStandardInduction.successorInstance phi)) := by
    simp only [phi,consTemplate,GorbowStandardInduction.successorInstance,substituteFormula,
      substDrop,substCons,substitute,successorLift,Fin.cases_zero]
    exact Hilbert.Local.finish (Hilbert.Local.discharge hout)
  have h := atTerm phi index (HistoryCodec.ArithmeticSupport.induction phi hb hs)
  rw [show phi = consTemplate tag ctag a b from rfl,consAt] at h
  exact ⟨h⟩

def nilTemplate (ctx tag : Nat) : Formula (ctx+1) := .equal (dropCall tag (.var 0) .zero) .zero

theorem dropNil {n ctx : Nat} (p : Program n) tag (ht : (nodes p)[tag]? = some ⟨2,drop⟩) (index : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (dropCall tag index .zero) .zero)) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let phi := nilTemplate ctx tag
  obtain ⟨hz⟩ := dropZero p tag ht (.zero : Term ctx)
  have hb : Derivation T (GorbowStandardInstances.instantiate phi .zero) := by
    simpa only [phi,nilTemplate,GorbowStandardInstances.instantiate,substituteFormula,substDrop,substitute,Fin.cases_zero] using hz
  let x : Term (ctx+1) := .var 0
  have hi : Hilbert.Local T (ctx+1) [phi] (.equal (dropCall tag x .zero) .zero) := .hypothesis List.mem_cons_self
  obtain ⟨hsucc⟩ := dropSuccessor p tag ht x .zero
  obtain ⟨htail⟩ := DestructorProof.destructorZero (ctx := ctx+1) p (tailTag tag) true (tailInstalled p tag ht)
  have hc := localUnary (call (tailTag tag) (.var 0 ::ᵥ nil)) _ _ hi
  simp only [Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,substitute,Fin.cases_zero] at hc
  have hout := localTrans _ _ _ (.base hsucc) (localTrans _ _ _ hc (.base htail))
  have hs : Derivation T (.imp phi (GorbowStandardInduction.successorInstance phi)) := by
    simp only [phi,nilTemplate,GorbowStandardInduction.successorInstance,substituteFormula,substDrop,substitute,Fin.cases_zero]
    exact Hilbert.Local.finish (Hilbert.Local.discharge hout)
  have h := atTerm phi index (HistoryCodec.ArithmeticSupport.induction phi hb hs)
  exact ⟨by simpa only [phi,nilTemplate,GorbowStandardInstances.instantiate,substituteFormula,substDrop,substitute,Fin.cases_zero] using h⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLookup.DropProof
