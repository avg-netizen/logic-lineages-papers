module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDifference.ShiftProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDifference.ArithmeticProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof
open GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open EquationsProof ShiftProof

private def cancelTemplate {ctx : Nat} (tag : Nat) (k : Term ctx) : Formula (ctx+1) :=
  .equal (differenceCall tag (.var 0) (.add (.var 0) (liftTerm k))) (liftTerm k)
private theorem cancelAt {ctx : Nat} tag (k a : Term ctx) :
    GorbowStandardInstances.instantiate (cancelTemplate tag k) a =
      .equal (differenceCall tag a (.add a k)) k := by
  simp only [GorbowStandardInstances.instantiate,cancelTemplate,substituteFormula,substituteDifference,
    substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

theorem differenceCancel : Targets.DifferenceCancel := by
  intro n p tag ht ctx a k
  let T := GorbowPRNumeralCalculation.Theory p
  let phi := cancelTemplate tag k
  obtain ⟨hz⟩ := differenceZero p tag ht (.add .zero k)
  have hb : Derivation T (GorbowStandardInstances.instantiate phi .zero) := by
    rw [show phi = cancelTemplate tag k from rfl,cancelAt]
    exact Logic.trans _ _ _ hz (zeroLeft k)
  obtain ⟨hshift⟩ := differenceShift n p tag ht (ctx+1) (.var 0) (.add (.var 0) (liftTerm k))
  have harg := congruentSecond (T := T) tag (.add (.succ (.var 0)) (liftTerm k))
    (.succ (.add (.var 0) (liftTerm k))) (.succ (.var 0)) (successorLeft (.var 0) (liftTerm k))
  have ih : Hilbert.Local T (ctx+1) [phi]
      (.equal (differenceCall tag (.var 0) (.add (.var 0) (liftTerm k))) (liftTerm k)) :=
    .hypothesis List.mem_cons_self
  have hs : Derivation T (.imp phi (GorbowStandardInduction.successorInstance phi)) := by
    change Derivation T (.imp phi (GorbowStandardInduction.successorInstance (cancelTemplate tag k)))
    simp only [GorbowStandardInduction.successorInstance,cancelTemplate,substituteFormula,
      substituteDifference,substitute,successorLift,Fin.cases_zero]
    exact Hilbert.Local.finish (Hilbert.Local.discharge
      (localTrans _ _ _ (.base (Logic.trans _ _ _ harg hshift)) ih))
  have h := atTerm phi a (HistoryCodec.ArithmeticSupport.induction phi hb hs)
  rw [show phi = cancelTemplate tag k from rfl,cancelAt] at h
  exact ⟨h⟩

private def absorbTemplate (ctx tag : Nat) : Formula (ctx+1) :=
  .equal (differenceCall tag (.var 0) .zero) .zero

theorem differenceAbsorb {n ctx : Nat} (p : Program n) tag
    (ht : (nodes p)[tag]? = some ⟨2,HistoryCodec.difference⟩) (a : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (differenceCall tag a .zero) .zero)) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let phi := absorbTemplate ctx tag
  obtain ⟨hz⟩ := differenceZero p tag ht (.zero : Term ctx)
  have hb : Derivation T (GorbowStandardInstances.instantiate phi .zero) := by
    simpa only [phi,absorbTemplate,GorbowStandardInstances.instantiate,substituteFormula,
      substituteDifference,substitute,Fin.cases_zero] using hz
  obtain ⟨hnext⟩ := differenceSuccessor p tag ht (.var 0 : Term (ctx+1)) .zero
  have hp := predecessorInstalled p tag ht
  obtain ⟨hpz⟩ := predecessorZero n p (predecessorTag tag) hp (ctx+1)
  have ih : Hilbert.Local T (ctx+1) [phi] (.equal (differenceCall tag (.var 0) .zero) .zero) :=
    .hypothesis List.mem_cons_self
  have hc := localPredecessor (predecessorTag tag) _ _ ih
  have hs : Derivation T (.imp phi (GorbowStandardInduction.successorInstance phi)) := by
    change Derivation T (.imp phi (GorbowStandardInduction.successorInstance (absorbTemplate ctx tag)))
    simp only [GorbowStandardInduction.successorInstance,absorbTemplate,substituteFormula,
      substituteDifference,substitute,Fin.cases_zero]
    exact Hilbert.Local.finish (Hilbert.Local.discharge
      (localTrans _ _ _ (.base hnext) (localTrans _ _ _ hc (.base hpz))))
  have h := atTerm phi a (HistoryCodec.ArithmeticSupport.induction phi hb hs)
  simpa only [phi,absorbTemplate,GorbowStandardInstances.instantiate,substituteFormula,
    substituteDifference,substitute,Fin.cases_zero] using (show Nonempty _ from ⟨h⟩)

private def saturateTemplate {ctx : Nat} (tag : Nat) (k : Term ctx) : Formula (ctx+1) :=
  .equal (differenceCall tag (.add (.var 0) (liftTerm k)) (.var 0)) .zero
private theorem saturateAt {ctx : Nat} tag (k b : Term ctx) :
    GorbowStandardInstances.instantiate (saturateTemplate tag k) b =
      .equal (differenceCall tag (.add b k) b) .zero := by
  simp only [GorbowStandardInstances.instantiate,saturateTemplate,substituteFormula,substituteDifference,
    substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

theorem differenceSaturate : Targets.DifferenceSaturate := by
  intro n p tag ht ctx b k
  let T := GorbowPRNumeralCalculation.Theory p
  let phi := saturateTemplate tag k
  obtain ⟨hz⟩ := differenceAbsorb p tag ht k
  have hb : Derivation T (GorbowStandardInstances.instantiate phi .zero) := by
    rw [show phi = saturateTemplate tag k from rfl,saturateAt]
    exact Logic.trans _ _ _ (congruentFirst tag (.add .zero k) k .zero (zeroLeft k)) hz
  obtain ⟨hshift⟩ := differenceShift n p tag ht (ctx+1) (.add (.var 0) (liftTerm k)) (.var 0)
  have harg := congruentFirst (T := T) tag (.add (.succ (.var 0)) (liftTerm k))
    (.succ (.add (.var 0) (liftTerm k))) (.succ (.var 0)) (successorLeft (.var 0) (liftTerm k))
  have ih : Hilbert.Local T (ctx+1) [phi]
      (.equal (differenceCall tag (.add (.var 0) (liftTerm k)) (.var 0)) .zero) :=
    .hypothesis List.mem_cons_self
  have hs : Derivation T (.imp phi (GorbowStandardInduction.successorInstance phi)) := by
    change Derivation T (.imp phi (GorbowStandardInduction.successorInstance (saturateTemplate tag k)))
    simp only [GorbowStandardInduction.successorInstance,saturateTemplate,substituteFormula,
      substituteDifference,substitute,successorLift,Fin.cases_zero]
    exact Hilbert.Local.finish (Hilbert.Local.discharge
      (localTrans _ _ _ (.base (Logic.trans _ _ _ harg hshift)) ih))
  have h := atTerm phi b (HistoryCodec.ArithmeticSupport.induction phi hb hs)
  rw [show phi = saturateTemplate tag k from rfl,saturateAt] at h
  exact ⟨h⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDifference.ArithmeticProof
