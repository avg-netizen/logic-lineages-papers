module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCancellation.OrderSupportProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCancellation.TransitivityProof
open GorbowSyntax GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open HistoryBounds HistoryBounds.SupportProof HistoryBounds.PairProof

theorem strictAdd (T : Sentence → Prop) {ctx : Nat} (a b c : Term ctx) :
    Nonempty (Derivation T (.imp (strictBound a b) (strictBound a (.add b c)))) := by
  let H := HistoryOrder.lowerBody a b
  have hh : Hilbert.Local T (ctx+1) [H]
      (.equal (liftTerm b) (.add (liftTerm a) (.succ (.var 0)))) := .hypothesis List.mem_cons_self
  have hc := localUnary (.add (.var 0) (liftTerm (liftTerm c))) _ _ hh
  simp only [substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] at hc
  have hr := Logic.unary (.add (liftTerm (liftTerm a)) (.var 0)) _ _
    (successorLeft (T := T) (.var 0 : Term (ctx+1)) (liftTerm c))
  simp only [substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] at hr
  have he := localTrans _ _ _ hc (.base (Logic.trans _ _ _
    (addAssoc (liftTerm a) (.succ (.var 0)) (liftTerm c)) hr))
  have hout : Hilbert.Local T (ctx+1) [H] (strictBound (liftTerm a) (.add (liftTerm b) (liftTerm c))) :=
    .mp (.base (strictIntro _ _ (.add (.var 0) (liftTerm c)))) he
  have hbody : Derivation T (.imp H (GorbowPACore.weaken (strictBound a (.add b c)))) := by
    simpa only [weakenStrict,liftTerm,renameTerm,substitute] using Hilbert.Local.finish (Hilbert.Local.discharge hout)
  exact HBQuantifier.existentialElimination T H (strictBound a (.add b c)) ⟨hbody⟩

theorem weakAddPositive (T : Sentence → Prop) {ctx : Nat} (a b c : Term ctx) :
    Nonempty (Derivation T (.imp (weakBound a b) (strictBound a (.add b (.succ c))))) := by
  obtain ⟨ha⟩ := weakAdd T a b c
  obtain ⟨hs⟩ := weakSuccessor T a (.add b c)
  have ht := Derivation.mp (strictTransport (T := T) a (.add b (.succ c)) (.succ (.add b c)))
    (.arithmetic (.addSucc b c))
  exact ⟨Hilbert.compose ht (Hilbert.compose hs ha)⟩

theorem weakTrans (T : Sentence → Prop) {ctx : Nat} (a b c : Term ctx) :
    Nonempty (Derivation T (.imp (weakBound a b) (.imp (weakBound b c) (weakBound a c)))) := by
  let H := HistoryOrder.upperBody c b
  let P := weakBound (liftTerm a) (liftTerm b)
  let V : Term (ctx+1) := .add (liftTerm b) (.var 0)
  obtain ⟨ha⟩ := weakAdd T (liftTerm a) (liftTerm b) (.var 0)
  have hh : Hilbert.Local T (ctx+1) [P,H] (.equal (liftTerm c) V) :=
    .hypothesis (by simp [H,V,HistoryOrder.upperBody,HistoryOrder.lowerBody])
  have hp : Hilbert.Local T (ctx+1) [P,H] P := .hypothesis List.mem_cons_self
  have hv := Hilbert.Local.mp (.base ha) hp
  have hout : Hilbert.Local T (ctx+1) [P,H] (weakBound (liftTerm a) (liftTerm c)) :=
    .mp (.mp (.base (weakTransport _ _ V)) hh) hv
  have hbody : Derivation T (.imp H (GorbowPACore.weaken (.imp (weakBound a b) (weakBound a c)))) := by
    simpa only [GorbowPACore.weaken,substituteFormula,substWeak,substStrict,liftTerm,renameTerm] using
      Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge hout))
  obtain ⟨h⟩ := HBQuantifier.existentialElimination T H (.imp (weakBound a b) (weakBound a c)) ⟨hbody⟩
  have hp : Hilbert.Local T ctx [weakBound b c,weakBound a b] (weakBound a b) := .hypothesis (by simp)
  have hq : Hilbert.Local T ctx [weakBound b c,weakBound a b] (weakBound b c) := .hypothesis List.mem_cons_self
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge
    (.mp (.mp (.base h) hq) hp)))⟩

theorem strictWeakTrans (T : Sentence → Prop) {ctx : Nat} (a b c : Term ctx) :
    Nonempty (Derivation T (.imp (strictBound a b) (.imp (weakBound b c) (strictBound a c)))) := by
  let H := HistoryOrder.upperBody c b
  let P := strictBound (liftTerm a) (liftTerm b)
  let V : Term (ctx+1) := .add (liftTerm b) (.var 0)
  obtain ⟨ha⟩ := strictAdd T (liftTerm a) (liftTerm b) (.var 0)
  have hh : Hilbert.Local T (ctx+1) [P,H] (.equal (liftTerm c) V) :=
    .hypothesis (by simp [H,V,HistoryOrder.upperBody,HistoryOrder.lowerBody])
  have hp : Hilbert.Local T (ctx+1) [P,H] P := .hypothesis List.mem_cons_self
  have hv := Hilbert.Local.mp (.base ha) hp
  have hout : Hilbert.Local T (ctx+1) [P,H] (strictBound (liftTerm a) (liftTerm c)) :=
    .mp (.mp (.base (strictTransport _ _ V)) hh) hv
  have hbody : Derivation T (.imp H (GorbowPACore.weaken (.imp (strictBound a b) (strictBound a c)))) := by
    simpa only [GorbowPACore.weaken,substituteFormula,substWeak,substStrict,liftTerm,renameTerm] using
      Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge hout))
  obtain ⟨h⟩ := HBQuantifier.existentialElimination T H (.imp (strictBound a b) (strictBound a c)) ⟨hbody⟩
  have hp : Hilbert.Local T ctx [weakBound b c,strictBound a b] (strictBound a b) := .hypothesis (by simp)
  have hq : Hilbert.Local T ctx [weakBound b c,strictBound a b] (weakBound b c) := .hypothesis List.mem_cons_self
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge
    (.mp (.mp (.base h) hq) hp)))⟩

theorem weakStrictTrans (T : Sentence → Prop) {ctx : Nat} (a b c : Term ctx) :
    Nonempty (Derivation T (.imp (weakBound a b) (.imp (strictBound b c) (strictBound a c)))) := by
  let H := HistoryOrder.lowerBody b c
  let P := weakBound (liftTerm a) (liftTerm b)
  let V : Term (ctx+1) := .add (liftTerm b) (.succ (.var 0))
  obtain ⟨ha⟩ := weakAddPositive T (liftTerm a) (liftTerm b) (.var 0)
  have hh : Hilbert.Local T (ctx+1) [P,H] (.equal (liftTerm c) V) :=
    .hypothesis (by simp [H,V,HistoryOrder.upperBody,HistoryOrder.lowerBody])
  have hp : Hilbert.Local T (ctx+1) [P,H] P := .hypothesis List.mem_cons_self
  have hv := Hilbert.Local.mp (.base ha) hp
  have hout : Hilbert.Local T (ctx+1) [P,H] (strictBound (liftTerm a) (liftTerm c)) :=
    .mp (.mp (.base (strictTransport _ _ V)) hh) hv
  have hbody : Derivation T (.imp H (GorbowPACore.weaken (.imp (weakBound a b) (strictBound a c)))) := by
    simpa only [GorbowPACore.weaken,substituteFormula,substWeak,substStrict,liftTerm,renameTerm] using
      Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge hout))
  obtain ⟨h⟩ := HBQuantifier.existentialElimination T H (.imp (weakBound a b) (strictBound a c)) ⟨hbody⟩
  have hp : Hilbert.Local T ctx [strictBound b c,weakBound a b] (weakBound a b) := .hypothesis (by simp)
  have hq : Hilbert.Local T ctx [strictBound b c,weakBound a b] (strictBound b c) := .hypothesis List.mem_cons_self
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge
    (.mp (.mp (.base h) hq) hp)))⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCancellation.TransitivityProof
