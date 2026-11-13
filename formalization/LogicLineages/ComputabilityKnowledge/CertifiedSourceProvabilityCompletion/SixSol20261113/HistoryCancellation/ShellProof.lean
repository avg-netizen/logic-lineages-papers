module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCancellation.TransitivityProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCancellation.SquareProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCancellation.ShellProof
open GorbowSyntax GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open HistoryBounds HistoryBounds.SupportProof HistoryBounds.PairProof OrderSupportProof TransitivityProof

def square {ctx : Nat} (a : Term ctx) : Term ctx := .mul a a
def top {ctx : Nat} (a : Term ctx) : Term ctx := .add (.add (square a) a) a

theorem strictToWeak (T : Sentence → Prop) {ctx : Nat} (a b : Term ctx) :
    Nonempty (Derivation T (.imp (strictBound a b) (weakBound a b))) := by
  let H := HistoryOrder.lowerBody a b
  have hh : Hilbert.Local T (ctx+1) [H]
      (.equal (liftTerm b) (.add (liftTerm a) (.succ (.var 0)))) := .hypothesis List.mem_cons_self
  have hout : Hilbert.Local T (ctx+1) [H] (weakBound (liftTerm a) (liftTerm b)) :=
    .mp (.base (weakIntro _ _ (.succ (.var 0)))) hh
  have hb : Derivation T (.imp H (GorbowPACore.weaken (weakBound a b))) := by
    rw [weakenWeak]
    exact Hilbert.Local.finish (Hilbert.Local.discharge hout)
  exact HBQuantifier.existentialElimination T H (weakBound a b) ⟨hb⟩

noncomputable def strictSuccessor {T : Sentence → Prop} {ctx : Nat} (a : Term ctx) :
    Derivation T (strictBound a (.succ a)) := by
  have he : Derivation T (.equal (.succ a) (.add a (.succ .zero))) :=
    Support.equalitySymmetry _ _ (Logic.trans _ _ _ (.arithmetic (.addSucc a .zero))
      (Logic.unary (.succ (.var 0)) _ _ (.arithmetic (.addZero a))))
  exact .mp (strictIntro a (.succ a) .zero) he

theorem squareStep (T : Sentence → Prop) {ctx : Nat} (a : Term ctx) :
    Nonempty (Derivation T (weakBound (square a) (square (.succ a)))) := by
  obtain ⟨h1⟩ := weakAdd T (square a) (square a) a
  obtain ⟨h2⟩ := weakAdd T (square a) (.add (square a) a) a
  obtain ⟨hs⟩ := weakSuccessor T (square a) (top a)
  have htop : Derivation T (strictBound (square a) (.succ (top a))) :=
    .mp hs (.mp h2 (.mp h1 (weakReflexive (square a))))
  have hstrict : Derivation T (strictBound (square a) (square (.succ a))) :=
    .mp (.mp (strictTransport _ _ _) (SquareProof.squareSuccessor a)) htop
  obtain ⟨hw⟩ := strictToWeak T (square a) (square (.succ a))
  exact ⟨.mp hw hstrict⟩

def separationTemplate {ctx : Nat} (a : Term ctx) : Formula (ctx+1) :=
  strictBound (top (liftTerm a)) (square (.add (liftTerm a) (.succ (.var 0))))

theorem separationAt {ctx : Nat} (a k : Term ctx) :
    GorbowStandardInstances.instantiate (separationTemplate a) k =
      strictBound (top a) (square (.add a (.succ k))) := by
  simp only [GorbowStandardInstances.instantiate,separationTemplate,substStrict,top,square,
    substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

/-- Genuine internal separation of the full shell at a from every later square. -/
theorem squareSeparation (T : Sentence → Prop) {ctx : Nat} (a k : Term ctx) :
    Nonempty (Derivation T (strictBound (top a) (square (.add a (.succ k))))) := by
  let phi := separationTemplate a
  have hzero : Derivation T (.equal (.add a (.succ .zero)) (.succ a)) :=
    Logic.trans _ _ _ (.arithmetic (.addSucc a .zero))
      (Logic.unary (.succ (.var 0)) _ _ (.arithmetic (.addZero a)))
  have hzsquare := Logic.unary (.mul (.var 0) (.var 0)) _ _ hzero
  have hb : Derivation T (GorbowStandardInstances.instantiate phi .zero) := by
    rw [show phi = separationTemplate a from rfl,separationAt]
    exact .mp (.mp (strictTransport _ _ _) (Logic.trans _ _ _ hzsquare (SquareProof.squareSuccessor a)))
      (strictSuccessor (top a))
  let A := liftTerm a
  let x : Term (ctx+1) := .var 0
  let old := square (.add A (.succ x))
  let next := square (.succ (.add A (.succ x)))
  obtain ⟨hstep⟩ := squareStep T (.add A (.succ x))
  obtain ⟨htrans⟩ := strictWeakTrans T (top A) old next
  have hi : Hilbert.Local T (ctx+1) [phi] (strictBound (top A) old) := .hypothesis List.mem_cons_self
  have hn := Hilbert.Local.mp (.mp (.base htrans) hi) (.base hstep)
  have he := Logic.unary (.mul (.var 0) (.var 0)) _ _
    (Derivation.arithmetic (A := T) (.addSucc A (.succ x)))
  have hout : Hilbert.Local T (ctx+1) [phi]
      (strictBound (top A) (square (.add A (.succ (.succ x))))) :=
    .mp (.mp (.base (strictTransport _ _ _)) (.base he)) hn
  have hs : Derivation T (.imp phi (GorbowStandardInduction.successorInstance phi)) := by
    simp only [phi,separationTemplate,GorbowStandardInduction.successorInstance,substStrict,
      top,square,substitute,successorLift,Fin.cases_zero]
    exact Hilbert.Local.finish (Hilbert.Local.discharge hout)
  have h := atTerm phi k (HistoryCodec.ArithmeticSupport.induction phi hb hs)
  rw [show phi = separationTemplate a from rfl,separationAt] at h
  exact ⟨h⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCancellation.ShellProof
