module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDifference.EquationsProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDifference.ShiftProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof
open GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open EquationsProof

theorem substituteDifference {m n : Nat} (sub : Fin m → Term n) tag (a b : Term m) :
    substitute sub (differenceCall tag a b) = differenceCall tag (substitute sub a) (substitute sub b) := by
  simp only [differenceCall,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil]

def localPredecessor {T : Sentence → Prop} {ctx : Nat} {gamma : List (Formula ctx)} tag
    (a b : Term ctx) (h : Hilbert.Local T ctx gamma (.equal a b)) :
    Hilbert.Local T ctx gamma (.equal (call tag (a ::ᵥ nil)) (call tag (b ::ᵥ nil))) := by
  have d := localUnary (call tag (.var 0 ::ᵥ nil)) a b h
  simpa only [Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,substitute,Fin.cases_zero] using d

def congruentFirst {T : Sentence → Prop} {ctx : Nat} tag (a b k : Term ctx)
    (h : Derivation T (.equal a b)) :
    Derivation T (.equal (differenceCall tag a k) (differenceCall tag b k)) := by
  have d := Logic.unary (differenceCall tag (.var 0) (liftTerm k)) a b h
  simpa only [substituteDifference,liftTerm,Support.shiftCancel,substitute,Fin.cases_zero] using d

def congruentSecond {T : Sentence → Prop} {ctx : Nat} tag (a b k : Term ctx)
    (h : Derivation T (.equal a b)) :
    Derivation T (.equal (differenceCall tag k a) (differenceCall tag k b)) := by
  have d := Logic.unary (differenceCall tag (liftTerm k) (.var 0)) a b h
  simpa only [substituteDifference,liftTerm,Support.shiftCancel,substitute,Fin.cases_zero] using d

private def template {ctx : Nat} (tag : Nat) (b : Term ctx) : Formula (ctx+1) :=
  .equal (differenceCall tag (.succ (.var 0)) (.succ (liftTerm b)))
    (differenceCall tag (.var 0) (liftTerm b))
private theorem templateAt {ctx : Nat} tag (b a : Term ctx) :
    GorbowStandardInstances.instantiate (template tag b) a =
      .equal (differenceCall tag (.succ a) (.succ b)) (differenceCall tag a b) := by
  simp only [GorbowStandardInstances.instantiate,template,substituteFormula,substituteDifference,
    substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

theorem differenceShift : Targets.DifferenceShift := by
  intro n p tag ht ctx a b
  let T := GorbowPRNumeralCalculation.Theory p
  let phi := template tag b
  have hp := predecessorInstalled p tag ht
  obtain ⟨hstart⟩ := differenceSuccessor p tag ht .zero (.succ b)
  obtain ⟨hz⟩ := differenceZero p tag ht (.succ b)
  obtain ⟨hpred⟩ := predecessorSuccessor n p (predecessorTag tag) hp ctx b
  obtain ⟨hend⟩ := differenceZero p tag ht b
  have hb : Derivation T (GorbowStandardInstances.instantiate phi .zero) := by
    rw [show phi = template tag b from rfl,templateAt]
    have hc := Logic.callCongruence T (predecessorTag tag)
      (differenceCall tag .zero (.succ b) ::ᵥ nil) (.succ b ::ᵥ nil)
      (fun i => by cases i using Fin.cases with | zero => exact hz | succ i => exact Fin.elim0 i)
    exact Logic.trans _ _ _ hstart (Logic.trans _ _ _ hc
      (Logic.trans _ _ _ hpred (Support.equalitySymmetry _ _ hend)))
  obtain ⟨hl⟩ := differenceSuccessor p tag ht (.succ (.var 0)) (.succ (liftTerm b))
  obtain ⟨hr⟩ := differenceSuccessor p tag ht (.var 0) (liftTerm b)
  have ih : Hilbert.Local T (ctx+1) [phi]
      (.equal (differenceCall tag (.succ (.var 0)) (.succ (liftTerm b)))
        (differenceCall tag (.var 0) (liftTerm b))) := .hypothesis List.mem_cons_self
  have hc := localPredecessor (predecessorTag tag) _ _ ih
  have hs : Derivation T (.imp phi (GorbowStandardInduction.successorInstance phi)) := by
    change Derivation T (.imp phi (GorbowStandardInduction.successorInstance (template tag b)))
    simp only [GorbowStandardInduction.successorInstance,template,substituteFormula,
      substituteDifference,substitute,successorLift,Fin.cases_zero]
    exact Hilbert.Local.finish (Hilbert.Local.discharge
      (localTrans _ _ _ (.base hl) (localTrans _ _ _ hc (.base (Support.equalitySymmetry _ _ hr)))))
  have h := atTerm phi a (HistoryCodec.ArithmeticSupport.induction phi hb hs)
  rw [show phi = template tag b from rfl,templateAt] at h
  exact ⟨h⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDifference.ShiftProof
