module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorDrain.Targets

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorDrain.BoundSupportProof
open GorbowSyntax GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open HistoryBounds HistoryBounds.SupportProof

theorem sumZeroLeft (T : Sentence → Prop) {ctx : Nat} (a b : Term ctx) :
    Nonempty (Derivation T (.imp (.equal (.add a b) .zero) (.equal a .zero))) := by
  let Q := Formula.imp (.equal (.add a b) .zero) (.equal a .zero)
  have he : Derivation T (.imp (.equal a .zero) Q) := .logical (.k _ _)
  let H := HistoryOrder.SupportProof.predBody a
  let E : Formula (ctx+1) := .equal (.add (liftTerm a) (liftTerm b)) .zero
  have hh : Hilbert.Local T (ctx+1) [E,H] (.equal (liftTerm a) (.succ (.var 0))) :=
    .hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
  have hz : Hilbert.Local T (ctx+1) [E,H] E := .hypothesis List.mem_cons_self
  have hc := localUnary (.add (.var 0) (liftTerm (liftTerm b))) _ _ hh
  simp only [substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] at hc
  have hs : Hilbert.Local T (ctx+1) [E,H] (.equal (.succ (.add (.var 0) (liftTerm b))) .zero) :=
    localTrans _ _ _ (.base (Support.equalitySymmetry _ _ (successorLeft (.var 0) (liftTerm b))))
      (localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ hc) hz)
  have hout : Hilbert.Local T (ctx+1) [E,H] (.equal (liftTerm a) .zero) :=
    Hilbert.Local.explosion _ hs (.base (.arithmetic (.succNotZero (.add (.var 0) (liftTerm b)))))
  have hb : Derivation T (.imp H (GorbowPACore.weaken Q)) := by
    simpa only [Q,E,GorbowPACore.weaken,substituteFormula,substitute,liftTerm,renameTerm] using
      Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge hout))
  obtain ⟨hp⟩ := HBQuantifier.existentialElimination T H Q ⟨hb⟩
  obtain ⟨hc⟩ := HistoryOrder.SupportProof.zeroOrSuccessor T a
  exact ⟨.mp (.mp (.mp (.logical (.orElim _ _ _)) he) hp) hc⟩

theorem weakZero (T : Sentence → Prop) {ctx : Nat} (a : Term ctx) :
    Nonempty (Derivation T (.imp (weakBound a .zero) (.equal a .zero))) := by
  let H := HistoryOrder.upperBody (.zero : Term ctx) a
  have hh : Hilbert.Local T (ctx+1) [H] (.equal (.zero : Term (ctx+1)) (.add (liftTerm a) (.var 0))) :=
    .hypothesis List.mem_cons_self
  obtain ⟨hs⟩ := sumZeroLeft T (liftTerm a) (.var (0 : Fin (ctx+1)))
  have hout : Hilbert.Local T (ctx+1) [H] (.equal (liftTerm a) .zero) :=
    .mp (.base hs) (HistoryOrder.StepProof.localSym _ _ hh)
  exact HBQuantifier.existentialElimination T H (.equal a .zero)
    ⟨Hilbert.Local.finish (Hilbert.Local.discharge hout)⟩

theorem weakSuccessorCancel (T : Sentence → Prop) {ctx : Nat} (a b : Term ctx) :
    Nonempty (Derivation T (.imp (weakBound (.succ a) (.succ b)) (weakBound a b))) := by
  let H := HistoryOrder.upperBody (.succ b) (.succ a)
  have hh : Hilbert.Local T (ctx+1) [H]
      (.equal (.succ (liftTerm b)) (.add (.succ (liftTerm a)) (.var 0))) := .hypothesis List.mem_cons_self
  have he := localTrans _ _ _ hh (.base (successorLeft (liftTerm a) (.var 0)))
  have hc : Hilbert.Local T (ctx+1) [H] (.equal (liftTerm b) (.add (liftTerm a) (.var 0))) :=
    .mp (.base (.arithmetic (.succInjective (liftTerm b) (.add (liftTerm a) (.var 0))))) he
  have hout : Hilbert.Local T (ctx+1) [H] (weakBound (liftTerm a) (liftTerm b)) :=
    .mp (.base (weakIntro _ _ (.var 0))) hc
  have hb : Derivation T (.imp H (GorbowPACore.weaken (weakBound a b))) := by
    rw [weakenWeak]
    exact Hilbert.Local.finish (Hilbert.Local.discharge hout)
  exact HBQuantifier.existentialElimination T H (weakBound a b) ⟨hb⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorDrain.BoundSupportProof
