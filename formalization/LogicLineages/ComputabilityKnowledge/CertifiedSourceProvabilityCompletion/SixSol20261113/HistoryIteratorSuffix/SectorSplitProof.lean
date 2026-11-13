module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorSuffix.Targets

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorSuffix.SectorSplitProof
open GorbowSyntax GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open HistoryBounds HistoryBounds.SupportProof

/-- A positive additive gap supplies a weak bound on the successor, internally. -/
theorem successorWeak (T : Sentence → Prop) {ctx : Nat} (a b : Term ctx) :
    Nonempty (Derivation T (.imp (strictBound a b) (weakBound (.succ a) b))) := by
  let H := HistoryOrder.lowerBody a b
  have hh : Hilbert.Local T (ctx+1) [H]
      (.equal (liftTerm b) (.add (liftTerm a) (.succ (.var 0)))) := .hypothesis List.mem_cons_self
  have he : Derivation T (.equal (.add (liftTerm a) (.succ (.var (0 : Fin (ctx+1)))))
      (.add (.succ (liftTerm a)) (.var 0))) :=
    Logic.trans _ _ _ (.arithmetic (.addSucc (liftTerm a) (.var 0)))
      (Support.equalitySymmetry _ _ (successorLeft (liftTerm a) (.var 0)))
  have hout : Hilbert.Local T (ctx+1) [H] (weakBound (.succ (liftTerm a)) (liftTerm b)) :=
    .mp (.base (weakIntro _ _ (.var 0))) (localTrans _ _ _ hh (.base he))
  have hb : Derivation T (.imp H (GorbowPACore.weaken (weakBound (.succ a) b))) := by
    simpa only [weakenWeak,liftTerm,renameTerm,substitute] using
      Hilbert.Local.finish (Hilbert.Local.discharge hout)
  exact HBQuantifier.existentialElimination T H (weakBound (.succ a) b) ⟨hb⟩

theorem lowerNext (T : Sentence → Prop) {ctx : Nat} (a b : Term ctx) :
    Nonempty (Derivation T (.imp (HistoryOrder.lower a b)
      (.disj (.equal b (.succ a)) (HistoryOrder.lower (.succ a) b)))) := by
  obtain ⟨hw⟩ := successorWeak T a b
  obtain ⟨hs⟩ := HistoryCancellation.TrichotomyProof.weakSplit T (.succ a) b
  exact ⟨Hilbert.compose hs hw⟩

theorem upperNext (T : Sentence → Prop) {ctx : Nat} (a b : Term ctx) :
    Nonempty (Derivation T (.imp (HistoryOrder.upper a b)
      (.disj (.equal a b) (HistoryOrder.upper a (.succ b))))) := by
  obtain ⟨hs⟩ := HistoryCancellation.TrichotomyProof.weakSplit T b a
  obtain ⟨hw⟩ := successorWeak T b a
  let Q := Formula.disj (.equal a b) (HistoryOrder.upper a (.succ b))
  have hl : Derivation T (.imp (.equal a b) Q) := .logical (.orLeft _ _)
  have hr : Derivation T (.imp (strictBound b a) Q) :=
    Hilbert.compose (.logical (.orRight _ _)) hw
  have he : Derivation T (.imp (.disj (.equal a b) (strictBound b a)) Q) :=
    .mp (.mp (.logical (.orElim _ _ _)) hl) hr
  exact ⟨Hilbert.compose he hs⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorSuffix.SectorSplitProof
