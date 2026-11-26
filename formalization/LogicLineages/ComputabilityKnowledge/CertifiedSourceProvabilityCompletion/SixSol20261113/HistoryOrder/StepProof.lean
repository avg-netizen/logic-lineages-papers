module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryOrder.SupportProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryOrder.StepProof
open GorbowSyntax GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport SupportProof

def split {ctx : Nat} (a b : Term ctx) : Formula ctx := .disj (lower a b) (upper a b)

theorem substSplit {m n : Nat} (sub : Fin m → Term n) (a b : Term m) :
    substituteFormula sub (split a b) = split (substitute sub a) (substitute sub b) := by
  simp only [split,substituteFormula,substLower,substUpper]

theorem weakenSplit {ctx : Nat} (a b : Term ctx) :
    GorbowPACore.weaken (split a b) = split (liftTerm a) (liftTerm b) := by
  rw [GorbowPACore.weaken,substSplit]
  rfl

noncomputable def localSym {T : Sentence → Prop} {ctx : Nat} {gamma : List (Formula ctx)} (a b : Term ctx)
    (h : Hilbert.Local T ctx gamma (.equal a b)) : Hilbert.Local T ctx gamma (.equal b a) :=
  .mp (.base (Logic.symmetryRule T a b)) h

def localAddRight {T : Sentence → Prop} {ctx : Nat} {gamma : List (Formula ctx)}
    (b s t : Term ctx) (h : Hilbert.Local T ctx gamma (.equal s t)) :
    Hilbert.Local T ctx gamma (.equal (.add b s) (.add b t)) := by
  have d := localUnary (.add (liftTerm b) (.var 0)) s t h
  simpa only [substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using d

noncomputable def selfSuccessorLower {T : Sentence → Prop} {ctx : Nat} (b : Term ctx) :
    Derivation T (lower b (.succ b)) := by
  have he : Derivation T (.equal (.add b (.succ .zero)) (.succ b)) :=
    Logic.trans _ _ _ (.arithmetic (.addSucc b .zero))
      (Logic.unary (.succ (.var 0)) _ _ (.arithmetic (.addZero b)))
  exact .mp (lowerIntro b (.succ b) .zero) (Support.equalitySymmetry _ _ he)

theorem lowerFirstAt {ctx : Nat} (a b : Term ctx) :
    GorbowStandardInstances.instantiate (lower (.var 0) (.succ (liftTerm b))) a =
      lower a (.succ b) := by
  simp only [GorbowStandardInstances.instantiate,substLower,substitute,
    liftTerm,Support.shiftCancel,Fin.cases_zero]

noncomputable def zeroGapStep {T : Sentence → Prop} {ctx : Nat} (a b k : Term ctx) :
    Derivation T (.imp (.equal k .zero) (.imp (.equal a (.add b k)) (split a (.succ b)))) := by
  let H := Formula.equal a (.add b k)
  let Z := Formula.equal k .zero
  have hh : Hilbert.Local T ctx [H,Z] H := .hypothesis List.mem_cons_self
  have hz : Hilbert.Local T ctx [H,Z] Z := .hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
  have hab := localTrans _ _ _ hh (localTrans _ _ _ (localAddRight b k .zero hz)
    (.base (.arithmetic (.addZero b))))
  have hr : Derivation T (.imp (.equal b a) (.imp (lower b (.succ b)) (lower a (.succ b)))) := by
    have d := Derivation.logical (A := T)
      (.equalityReplace (lower (.var 0) (.succ (liftTerm b))) b a)
    rwa [GorbowPACore.logicalFormula,lowerFirstAt,lowerFirstAt] at d
  have hl : Hilbert.Local T ctx [H,Z] (lower a (.succ b)) :=
    .mp (.mp (.base hr) (localSym a b hab)) (.base (selfSuccessorLower b))
  have hout : Hilbert.Local T ctx [H,Z] (split a (.succ b)) :=
    .mp (.base (.logical (.orLeft _ _))) hl
  exact Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge hout))

noncomputable def positiveGapStep {T : Sentence → Prop} {ctx : Nat} (a b k j : Term ctx) :
    Derivation T (.imp (.equal k (.succ j)) (.imp (.equal a (.add b k)) (split a (.succ b)))) := by
  let H := Formula.equal a (.add b k)
  let Z := Formula.equal k (.succ j)
  have hh : Hilbert.Local T ctx [H,Z] H := .hypothesis List.mem_cons_self
  have hz : Hilbert.Local T ctx [H,Z] Z := .hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
  have hsum : Derivation T (.equal (.add b (.succ j)) (.add (.succ b) j)) :=
    Logic.trans _ _ _ (.arithmetic (.addSucc b j))
      (Support.equalitySymmetry _ _ (successorLeft b j))
  have hgap := localTrans _ _ _ hh
    (localTrans _ _ _ (localAddRight b k (.succ j) hz) (.base hsum))
  have hu : Hilbert.Local T ctx [H,Z] (upper a (.succ b)) :=
    .mp (.base (upperIntro a (.succ b) j)) hgap
  have hout : Hilbert.Local T ctx [H,Z] (split a (.succ b)) :=
    .mp (.base (.logical (.orRight _ _))) hu
  exact Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge hout))

theorem gapStep (T : Sentence → Prop) {ctx : Nat} (a b k : Term ctx) :
    Nonempty (Derivation T (.imp (.equal a (.add b k)) (split a (.succ b)))) := by
  let H := Formula.equal a (.add b k)
  let B := Formula.imp H (split a (.succ b))
  have hp : Derivation T (.imp (predBody k) (GorbowPACore.weaken B)) := by
    have d := positiveGapStep (T := T) (liftTerm a) (liftTerm b) (liftTerm k) (.var 0)
    simpa only [B,H,predBody,GorbowPACore.weaken,substituteFormula,substSplit,substitute,
      liftTerm,renameTerm] using d
  obtain ⟨he⟩ := HBQuantifier.existentialElimination T (predBody k) B ⟨hp⟩
  have hz := zeroGapStep (T := T) a b k
  obtain ⟨hcases⟩ := zeroOrSuccessor T k
  exact ⟨.mp (.mp (.mp (.logical (.orElim _ _ _)) hz) he) hcases⟩

theorem upperSuccessor (T : Sentence → Prop) {ctx : Nat} (a b : Term ctx) :
    Nonempty (Derivation T (.imp (upper a b) (split a (.succ b)))) := by
  obtain ⟨hg⟩ := gapStep T (liftTerm a) (liftTerm b) (.var 0)
  have hh : Derivation T (.imp (upperBody a b) (GorbowPACore.weaken (split a (.succ b)))) := by
    simpa only [upperBody,weakenSplit,liftTerm,renameTerm,substitute] using hg
  exact HBQuantifier.existentialElimination T (upperBody a b) (split a (.succ b)) ⟨hh⟩

theorem lowerSuccessor (T : Sentence → Prop) {ctx : Nat} (a b : Term ctx) :
    Nonempty (Derivation T (.imp (lower a b) (lower a (.succ b)))) := by
  let H := lowerBody a b
  have hh : Hilbert.Local T (ctx+1) [H]
      (.equal (liftTerm b) (.add (liftTerm a) (.succ (.var 0)))) := .hypothesis List.mem_cons_self
  have hc := localUnary (.succ (.var 0)) _ _ hh
  have he : Hilbert.Local T (ctx+1) [H]
      (.equal (.succ (liftTerm b)) (.add (liftTerm a) (.succ (.succ (.var 0))))) :=
    localTrans _ _ _ hc (.base (Support.equalitySymmetry _ _
      (.arithmetic (.addSucc (liftTerm a) (.succ (.var 0))))))
  have hl : Hilbert.Local T (ctx+1) [H] (lower (liftTerm a) (.succ (liftTerm b))) :=
    .mp (.base (lowerIntro (liftTerm a) (.succ (liftTerm b)) (.succ (.var 0)))) he
  have hr : Derivation T (.imp (lowerBody a b) (GorbowPACore.weaken (lower a (.succ b)))) := by
    simpa only [weakenLower,liftTerm,renameTerm,substitute] using
      Hilbert.Local.finish (Hilbert.Local.discharge hl)
  exact HBQuantifier.existentialElimination T (lowerBody a b) (lower a (.succ b)) ⟨hr⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryOrder.StepProof
