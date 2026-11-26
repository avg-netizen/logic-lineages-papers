module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCancellation.IntervalProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCancellation.TrichotomyProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCancellation.SeparationProof
open GorbowSyntax GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open HistoryBounds HistoryBounds.SupportProof HistoryBounds.PairProof
open OrderSupportProof TransitivityProof ShellProof MonotonicityProof

theorem orderSeparation (T : Sentence → Prop) {ctx : Nat} (a b : Term ctx) :
    Nonempty (Derivation T (.imp (strictBound a b) (strictBound (top a) (square b)))) := by
  let H := HistoryOrder.lowerBody a b
  let v : Term (ctx+1) := .add (liftTerm a) (.succ (.var 0))
  obtain ⟨hsep⟩ := squareSeparation T (liftTerm a) (.var 0)
  have hh : Hilbert.Local T (ctx+1) [H] (.equal (liftTerm b) v) := .hypothesis List.mem_cons_self
  have he := localUnary (.mul (.var 0) (.var 0)) _ _ hh
  have hout : Hilbert.Local T (ctx+1) [H] (strictBound (top (liftTerm a)) (square (liftTerm b))) :=
    .mp (.mp (.base (strictTransport _ _ _)) he) (.base hsep)
  have hb : Derivation T (.imp H (GorbowPACore.weaken (strictBound (top a) (square b)))) := by
    simpa only [weakenStrict,top,square,liftTerm,renameTerm,substitute] using
      Hilbert.Local.finish (Hilbert.Local.discharge hout)
  exact HBQuantifier.existentialElimination T H (strictBound (top a) (square b)) ⟨hb⟩

/-- Incompatible shell intervals eliminate to any formula, using only PA. -/
theorem separatedElim (T : Sentence → Prop) {ctx : Nat} (a b x y : Term ctx) (Q : Formula ctx) :
    Nonempty (Derivation T (.imp (strictBound a b)
      (.imp (weakBound x (top a)) (.imp (weakBound (square b) y) (.imp (.equal x y) Q))))) := by
  let S := strictBound a b
  let U := weakBound x (top a)
  let L := weakBound (square b) y
  let E := Formula.equal x y
  obtain ⟨hsep⟩ := orderSeparation T a b
  obtain ⟨hw⟩ := weakTrans T (square b) y (top a)
  obtain ⟨ht⟩ := strictWeakTrans T (top a) (square b) (top a)
  obtain ⟨hn⟩ := strictIrreflexive T (top a)
  have hs : Hilbert.Local T ctx [E,L,U,S] S := .hypothesis (by simp)
  have hu : Hilbert.Local T ctx [E,L,U,S] U := .hypothesis (by simp)
  have hl : Hilbert.Local T ctx [E,L,U,S] L := .hypothesis (by simp)
  have he : Hilbert.Local T ctx [E,L,U,S] E := .hypothesis List.mem_cons_self
  have hy : Hilbert.Local T ctx [E,L,U,S] (weakBound y (top a)) :=
    .mp (.mp (.base (weakChildTransport _ _ _)) (HistoryOrder.StepProof.localSym _ _ he)) hu
  have hback := Hilbert.Local.mp (.mp (.base hw) hl) hy
  have hloop := Hilbert.Local.mp (.mp (.base ht) (.mp (.base hsep) hs)) hback
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge
    (Hilbert.Local.discharge (Hilbert.Local.discharge
      (Hilbert.Local.explosion Q hloop (.base hn))))))⟩

theorem sameMajor (T : Sentence → Prop) {ctx : Nat} (a b x y : Term ctx) :
    Nonempty (Derivation T (.imp (weakBound (square a) x) (.imp (weakBound x (top a))
      (.imp (weakBound (square b) y) (.imp (weakBound y (top b))
        (.imp (.equal x y) (.equal a b))))))) := by
  let A := weakBound (square a) x
  let B := weakBound x (top a)
  let C := weakBound (square b) y
  let D := weakBound y (top b)
  let E := Formula.equal x y
  let Q := Formula.equal a b
  let G := [E,D,C,B,A]
  obtain ⟨hab⟩ := separatedElim T a b x y Q
  obtain ⟨hba⟩ := separatedElim T b a y x Q
  obtain ⟨htri⟩ := TrichotomyProof.trichotomy T a b
  have hl : Hilbert.Local T ctx G (.imp (strictBound a b) Q) := by
    have hs : Hilbert.Local T ctx (strictBound a b :: G) (strictBound a b) := .hypothesis List.mem_cons_self
    have hu : Hilbert.Local T ctx (strictBound a b :: G) B := .hypothesis (by simp [G])
    have hf : Hilbert.Local T ctx (strictBound a b :: G) C := .hypothesis (by simp [G])
    have he : Hilbert.Local T ctx (strictBound a b :: G) E := .hypothesis (by simp [G])
    exact Hilbert.Local.discharge (.mp (.mp (.mp (.mp (.base hab) hs) hu) hf) he)
  have hr : Hilbert.Local T ctx G (.imp (strictBound b a) Q) := by
    have hs : Hilbert.Local T ctx (strictBound b a :: G) (strictBound b a) := .hypothesis List.mem_cons_self
    have hu : Hilbert.Local T ctx (strictBound b a :: G) D := .hypothesis (by simp [G])
    have hf : Hilbert.Local T ctx (strictBound b a :: G) A := .hypothesis (by simp [G])
    have he : Hilbert.Local T ctx (strictBound b a :: G) E := .hypothesis (by simp [G])
    exact Hilbert.Local.discharge (.mp (.mp (.mp (.mp (.base hba) hs) hu) hf)
      (HistoryOrder.StepProof.localSym _ _ he))
  have hrest : Hilbert.Local T ctx G (.imp (.disj Q (strictBound b a)) Q) :=
    .mp (.mp (.base (.logical (.orElim _ _ _))) (.base (Hilbert.identity Q))) hr
  have hout : Hilbert.Local T ctx G Q :=
    .mp (.mp (.mp (.base (.logical (.orElim _ _ _))) hl) hrest) (.base htri)
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge
    (Hilbert.Local.discharge (Hilbert.Local.discharge (Hilbert.Local.discharge hout)))))⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCancellation.SeparationProof
