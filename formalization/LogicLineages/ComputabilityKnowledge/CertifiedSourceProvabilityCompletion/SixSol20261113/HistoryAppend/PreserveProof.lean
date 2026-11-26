module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryAppend.PreserveSupportProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryAppend.PreserveProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport PreserveSupportProof

/-- Code induction closes the zero-index case over ALL source histories.
The successor case does not assume any reconstruction equation. -/
theorem zeroIndexAll {n ctx : Nat} (p : Program n) atag ltag
    (ha : (nodes p)[atag]? = some ⟨2,append⟩)
    (hl : (nodes p)[ltag]? = some ⟨2,HistoryLookup.lookup⟩) (right entry : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (allPreserve atag ltag .zero right entry)) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let phi := preserve atag ltag .zero (.var 0) (liftTerm right) (liftTerm entry)
  obtain ⟨hn⟩ := nilPreserve p atag ltag hl (.zero : Term ctx) right entry
  have hb : Derivation T (GorbowStandardInstances.instantiate phi .zero) := by
    simpa only [phi,GorbowStandardInstances.instantiate,substPreserve,substitute,liftTerm,
      Support.shiftCancel,Fin.cases_zero] using hn
  obtain ⟨hp⟩ := positiveZeroPreserve p atag ltag ha hl (.var 0 : Term (ctx+1)) (liftTerm right) (liftTerm entry)
  have hs : Derivation T (.imp phi (GorbowStandardInduction.successorInstance phi)) := by
    simp only [phi,GorbowStandardInduction.successorInstance,substPreserve,substitute,successorLift,Fin.cases_zero]
    exact Hilbert.lift _ hp
  exact ⟨HistoryCodec.ArithmeticSupport.induction phi hb hs⟩

/-- Generalize only closed derivations: ALL code (IH → next) is obtained by
PA induction, then allDistribute/allVacuous give IH → ALL code next. -/
theorem successorAll {n ctx : Nat} (p : Program n) atag ltag
    (ha : (nodes p)[atag]? = some ⟨2,append⟩)
    (hl : (nodes p)[ltag]? = some ⟨2,HistoryLookup.lookup⟩) (index right entry : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.imp (allPreserve atag ltag index right entry) (allPreserve atag ltag (.succ index) right entry))) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let P := allPreserve atag ltag index right entry
  let Q := preserve atag ltag (.succ (liftTerm index)) (.var 0) (liftTerm right) (liftTerm entry)
  let phi := Formula.imp (allPreserve atag ltag (liftTerm index) (liftTerm right) (liftTerm entry)) Q
  obtain ⟨hn⟩ := nilPreserve p atag ltag hl (.succ index) right entry
  have hb : Derivation T (GorbowStandardInstances.instantiate phi .zero) := by
    simp only [phi,Q,GorbowStandardInstances.instantiate,substituteFormula,substAll,substPreserve,
      substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]
    exact Hilbert.lift P hn
  obtain ⟨hp⟩ := positiveSuccessorPreserve p atag ltag ha hl (liftTerm index) (.var 0 : Term (ctx+1))
    (liftTerm right) (liftTerm entry)
  have hs : Derivation T (.imp phi (GorbowStandardInduction.successorInstance phi)) := by
    simp only [phi,Q,GorbowStandardInduction.successorInstance,substituteFormula,substAll,substPreserve,
      substitute,successorLift,Fin.cases_zero]
    exact Hilbert.lift _ hp
  have hall := HistoryCodec.ArithmeticSupport.induction phi hb hs
  have hall' : Derivation T (.all (.imp (GorbowPACore.weaken P) Q)) := by
    simpa only [P,weakenAll,phi] using hall
  have hdist : Derivation T (.imp (.all (GorbowPACore.weaken P)) (.all Q)) :=
    .mp (.logical (.allDistribute (GorbowPACore.weaken P) Q)) hall'
  exact ⟨Hilbert.compose hdist (.logical (.allVacuous P))⟩

def template {ctx : Nat} (atag ltag : Nat) (right entry : Term ctx) : Formula (ctx+1) :=
  allPreserve atag ltag (.var 0) (liftTerm right) (liftTerm entry)

theorem templateAt {ctx : Nat} atag ltag (right entry index : Term ctx) :
    GorbowStandardInstances.instantiate (template atag ltag right entry) index =
      allPreserve atag ltag index right entry := by
  simp only [GorbowStandardInstances.instantiate,template,substAll,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

/-- Full frozen successful-reference preservation. The induction hypothesis
quantifies over the history code, so it legitimately applies to tail(code). -/
theorem internalPreserveSome : Targets.InternalPreserveSome := by
  intro n p atag ltag ha hl ctx index left right entry
  let T := GorbowPRNumeralCalculation.Theory p
  let phi := template atag ltag right entry
  obtain ⟨hz⟩ := zeroIndexAll p atag ltag ha hl right entry
  have hb : Derivation T (GorbowStandardInstances.instantiate phi .zero) := by
    rw [show phi = template atag ltag right entry from rfl,templateAt]
    exact hz
  obtain ⟨hstep⟩ := successorAll p atag ltag ha hl (.var 0 : Term (ctx+1)) (liftTerm right) (liftTerm entry)
  have hs : Derivation T (.imp phi (GorbowStandardInduction.successorInstance phi)) := by
    simp only [phi,template,GorbowStandardInduction.successorInstance,substAll,substitute,successorLift,Fin.cases_zero]
    exact hstep
  have h := atTerm phi index (HistoryCodec.ArithmeticSupport.induction phi hb hs)
  rw [show phi = template atag ltag right entry from rfl,templateAt] at h
  exact ⟨.mp (allElim atag ltag index left right entry) h⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryAppend.PreserveProof
