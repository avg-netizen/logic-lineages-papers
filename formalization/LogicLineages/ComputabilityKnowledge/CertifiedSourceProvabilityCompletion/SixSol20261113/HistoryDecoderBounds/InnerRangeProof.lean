module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDecoderBounds.StepRangeProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDecoderBounds.InnerRangeProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport HistoryBounds HistoryBounds.SupportProof
open HistoryCancellation.MonotonicityProof HistoryDecoder.InnerEquationsProof

def template {ctx : Nat} (tag : Nat) (a code seed bound : Term ctx) : Formula (ctx+1) :=
  .imp (weakBound (.var 0) (liftTerm bound))
    (.imp (weakBound (liftTerm seed) (liftTerm bound))
      (weakBound (innerCall tag (.var 0) (liftTerm a) (liftTerm code) (liftTerm seed)) (liftTerm bound)))

theorem templateAt {ctx : Nat} tag (a code seed bound count : Term ctx) :
    GorbowStandardInstances.instantiate (template tag a code seed bound) count =
      .imp (weakBound count bound) (.imp (weakBound seed bound) (weakBound (innerCall tag count a code seed) bound)) := by
  simp only [GorbowStandardInstances.instantiate,template,substituteFormula,substWeak,substInner,
    substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

theorem innerRange {n ctx : Nat} (p : Program n) tag
    (ht : (nodes p)[tag]? = some ⟨4,HistoryDecoder.inner true⟩) (count a code seed bound : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.imp (weakBound count bound) (.imp (weakBound seed bound) (weakBound (innerCall tag count a code seed) bound)))) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let phi := template tag a code seed bound
  obtain ⟨hz⟩ := innerZero p tag true ht a code seed
  have hb : Derivation T (GorbowStandardInstances.instantiate phi .zero) := by
    rw [show phi = template tag a code seed bound from rfl,templateAt]
    have hs : Hilbert.Local T ctx [weakBound seed bound,weakBound .zero bound] (weakBound seed bound) := .hypothesis List.mem_cons_self
    exact Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge
      (.mp (.mp (.base (weakChildTransport _ _ _)) (.base hz)) hs)))
  let A := liftTerm a
  let C := liftTerm code
  let S := liftTerm seed
  let B := liftTerm bound
  let x : Term (ctx+1) := .var 0
  let P := weakBound (.succ x) B
  let R := weakBound S B
  let previous := innerCall tag x A C S
  have hi : Hilbert.Local T (ctx+1) [R,P,phi] phi := .hypothesis (by simp)
  have hp : Hilbert.Local T (ctx+1) [R,P,phi] P := .hypothesis (by simp)
  have hr : Hilbert.Local T (ctx+1) [R,P,phi] R := .hypothesis List.mem_cons_self
  obtain ⟨hweak⟩ := HistoryCancellation.ShellProof.strictToWeak T x (.succ x)
  have hxs := Derivation.mp hweak (HistoryCancellation.ShellProof.strictSuccessor x)
  obtain ⟨htrans⟩ := HistoryCancellation.TransitivityProof.weakTrans T x (.succ x) B
  have hx := Hilbert.Local.mp (.mp (.base htrans) (.base hxs)) hp
  have hprev := Hilbert.Local.mp (.mp hi hx) hr
  obtain ⟨hstep⟩ := StepRangeProof.stepRange p (innerStepTag tag) (stepInstalled p tag true ht) A x previous C S B
  have hstepBound := Hilbert.Local.mp (.mp (.base hstep) hprev) hx
  obtain ⟨hsucc⟩ := innerSuccessor p tag true ht x A C S
  have hout := Hilbert.Local.mp (.mp (.base (weakChildTransport _ _ _)) (.base hsucc)) hstepBound
  have hs : Derivation T (.imp phi (GorbowStandardInduction.successorInstance phi)) := by
    simp only [phi,template,GorbowStandardInduction.successorInstance,substituteFormula,
      substWeak,substInner,substitute,successorLift,Fin.cases_zero]
    exact Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge (Hilbert.Local.discharge hout)))
  have h := atTerm phi count (HistoryCodec.ArithmeticSupport.induction phi hb hs)
  rw [show phi = template tag a code seed bound from rfl,templateAt] at h
  exact ⟨h⟩

/-- Complete inclusive scan has all enumerated coordinates at most code. -/
theorem innerCompleteRange {n ctx : Nat} (p : Program n) tag
    (ht : (nodes p)[tag]? = some ⟨4,HistoryDecoder.inner true⟩) (a code seed : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.imp (weakBound seed code) (weakBound (innerCall tag (.succ code) a code seed) code))) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let H := weakBound seed code
  let previous := innerCall tag code a code seed
  obtain ⟨hr⟩ := innerRange p tag ht code a code seed code
  obtain ⟨hs⟩ := StepRangeProof.stepRange p (innerStepTag tag) (stepInstalled p tag true ht) a code previous code seed code
  obtain ⟨he⟩ := innerSuccessor p tag true ht code a code seed
  have hh : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
  have href := HistoryCancellation.OrderSupportProof.weakReflexive (T := T) code
  have hp := Hilbert.Local.mp (.mp (.base hr) (.base href)) hh
  have hstep := Hilbert.Local.mp (.mp (.base hs) hp) (.base href)
  have hout := Hilbert.Local.mp (.mp (.base (weakChildTransport _ _ _)) (.base he)) hstep
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge hout)⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDecoderBounds.InnerRangeProof
