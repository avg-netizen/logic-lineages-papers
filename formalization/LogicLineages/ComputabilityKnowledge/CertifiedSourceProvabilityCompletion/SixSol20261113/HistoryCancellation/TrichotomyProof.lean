module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCancellation.ShellProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCancellation.TrichotomyProof
open GorbowSyntax GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open HistoryBounds HistoryBounds.SupportProof HistoryBounds.PairProof

def splitValue {ctx : Nat} (a b : Term ctx) : Formula ctx :=
  .disj (.equal b a) (strictBound a b)

theorem substSplit {m n : Nat} (sub : Fin m → Term n) (a b : Term m) :
    substituteFormula sub (splitValue a b) = splitValue (substitute sub a) (substitute sub b) := by
  simp only [splitValue,substituteFormula,substStrict]

theorem valueAt {ctx : Nat} (a b : Term ctx) :
    GorbowStandardInstances.instantiate (splitValue (liftTerm a) (.var 0)) b = splitValue a b := by
  simp only [GorbowStandardInstances.instantiate,substSplit,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

def template {ctx : Nat} (a : Term ctx) : Formula (ctx+1) :=
  splitValue (liftTerm a) (.add (liftTerm a) (.var 0))

theorem templateAt {ctx : Nat} (a k : Term ctx) :
    GorbowStandardInstances.instantiate (template a) k = splitValue a (.add a k) := by
  simp only [GorbowStandardInstances.instantiate,template,substSplit,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

noncomputable def gapSplit {T : Sentence → Prop} {ctx : Nat} (a k : Term ctx) :
    Derivation T (splitValue a (.add a k)) := by
  let phi := template a
  have hb : Derivation T (GorbowStandardInstances.instantiate phi .zero) := by
    rw [show phi = template a from rfl,templateAt]
    exact .mp (.logical (.orLeft _ _)) (.arithmetic (.addZero a))
  have hpos : Derivation T (strictBound (liftTerm a) (.add (liftTerm a) (.succ (.var (0 : Fin (ctx+1)))))) :=
    .mp (strictIntro _ _ (.var 0)) (.logical (.reflexive _))
  have hs : Derivation T (.imp phi (GorbowStandardInduction.successorInstance phi)) := by
    simp only [phi,template,GorbowStandardInduction.successorInstance,substSplit,substitute,successorLift,Fin.cases_zero]
    exact Hilbert.lift _ (.mp (.logical (.orRight _ _)) hpos)
  have h := atTerm phi k (HistoryCodec.ArithmeticSupport.induction phi hb hs)
  rwa [show phi = template a from rfl,templateAt] at h

theorem weakSplit (T : Sentence → Prop) {ctx : Nat} (a b : Term ctx) :
    Nonempty (Derivation T (.imp (weakBound a b) (splitValue a b))) := by
  let H := HistoryOrder.upperBody b a
  let v : Term (ctx+1) := .add (liftTerm a) (.var 0)
  have hh : Hilbert.Local T (ctx+1) [H] (.equal (liftTerm b) v) := .hypothesis List.mem_cons_self
  have hr : Derivation T (.imp (.equal v (liftTerm b)) (.imp (splitValue (liftTerm a) v) (splitValue (liftTerm a) (liftTerm b)))) := by
    have h := Derivation.logical (A := T)
      (.equalityReplace (splitValue (liftTerm (liftTerm a)) (.var 0)) v (liftTerm b))
    rwa [GorbowPACore.logicalFormula,valueAt,valueAt] at h
  have hout : Hilbert.Local T (ctx+1) [H] (splitValue (liftTerm a) (liftTerm b)) :=
    .mp (.mp (.base hr) (HistoryOrder.StepProof.localSym _ _ hh)) (.base (gapSplit _ (.var 0)))
  have hb : Derivation T (.imp H (GorbowPACore.weaken (splitValue a b))) := by
    simpa only [GorbowPACore.weaken,substSplit,liftTerm,renameTerm] using
      Hilbert.Local.finish (Hilbert.Local.discharge hout)
  exact HBQuantifier.existentialElimination T H (splitValue a b) ⟨hb⟩

theorem trichotomy (T : Sentence → Prop) {ctx : Nat} (a b : Term ctx) :
    Nonempty (Derivation T (.disj (strictBound a b) (.disj (.equal a b) (strictBound b a)))) := by
  obtain ⟨hs⟩ := HistoryOrder.SplitProof.additiveSplit T ctx a b
  obtain ⟨hw⟩ := weakSplit T b a
  have hl : Derivation T (.imp (strictBound a b) (.disj (strictBound a b) (splitValue b a))) :=
    .logical (.orLeft _ _)
  have hr : Derivation T (.imp (weakBound b a) (.disj (strictBound a b) (splitValue b a))) :=
    Hilbert.compose (.logical (.orRight _ _)) hw
  exact ⟨.mp (.mp (.mp (.logical (.orElim _ _ _)) hl) hr) hs⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCancellation.TrichotomyProof
