module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryBounds.SupportProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryBounds.PairProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof
open GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport SupportProof

theorem weakValueAt {ctx : Nat} (child value : Term ctx) :
    GorbowStandardInstances.instantiate (weakBound (liftTerm child) (.var 0)) value =
      weakBound child value := by
  simp only [GorbowStandardInstances.instantiate,substWeak,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

theorem strictValueAt {ctx : Nat} (child value : Term ctx) :
    GorbowStandardInstances.instantiate (strictBound (liftTerm child) (.var 0)) value =
      strictBound child value := by
  simp only [GorbowStandardInstances.instantiate,substStrict,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

noncomputable def weakTransport {T : Sentence → Prop} {ctx : Nat} (child code value : Term ctx) :
    Derivation T (.imp (.equal code value) (.imp (weakBound child value) (weakBound child code))) := by
  have hr := Derivation.logical (A := T)
    (.equalityReplace (weakBound (liftTerm child) (.var 0)) value code)
  rw [GorbowPACore.logicalFormula,weakValueAt,weakValueAt] at hr
  exact Hilbert.compose hr (Logic.symmetryRule T code value)

noncomputable def strictTransport {T : Sentence → Prop} {ctx : Nat} (child code value : Term ctx) :
    Derivation T (.imp (.equal code value) (.imp (strictBound child value) (strictBound child code))) := by
  have hr := Derivation.logical (A := T)
    (.equalityReplace (strictBound (liftTerm child) (.var 0)) value code)
  rw [GorbowPACore.logicalFormula,strictValueAt,strictValueAt] at hr
  exact Hilbert.compose hr (Logic.symmetryRule T code value)

theorem pairBound {n ctx : Nat} (p : Program n) tag
    (ht : (nodes p)[tag]? = some ⟨2,HistoryCodec.pair⟩) (a b child : Term ctx)
    (hlow : Derivation (GorbowPRNumeralCalculation.Theory p) (weakBound child (.add (.mul b b) a)))
    (hhigh : Derivation (GorbowPRNumeralCalculation.Theory p) (weakBound child (.add (.add (.mul a a) a) b))) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (weakBound child (call tag (a ::ᵥ b ::ᵥ nil)))) := by
  let T := GorbowPRNumeralCalculation.Theory p
  obtain ⟨hl⟩ := HistoryOrder.PairProof.pairLowerOrder n p tag ht ctx a b
  obtain ⟨hu⟩ := HistoryOrder.PairProof.pairUpperOrder n p tag ht ctx a b
  obtain ⟨hc⟩ := HistoryOrder.SplitProof.additiveSplit T ctx a b
  have hleft : Derivation T (.imp (HistoryOrder.lower a b) (weakBound child (call tag (a ::ᵥ b ::ᵥ nil)))) := by
    have h : Hilbert.Local T ctx [HistoryOrder.lower a b] (HistoryOrder.lower a b) :=
      .hypothesis List.mem_cons_self
    have he := Hilbert.Local.mp (.base hl) h
    have out := Hilbert.Local.mp (.mp (.base (weakTransport child _ _)) he) (.base hlow)
    exact Hilbert.Local.finish (Hilbert.Local.discharge out)
  have hright : Derivation T (.imp (HistoryOrder.upper a b) (weakBound child (call tag (a ::ᵥ b ::ᵥ nil)))) := by
    have h : Hilbert.Local T ctx [HistoryOrder.upper a b] (HistoryOrder.upper a b) :=
      .hypothesis List.mem_cons_self
    have he := Hilbert.Local.mp (.base hu) h
    have out := Hilbert.Local.mp (.mp (.base (weakTransport child _ _)) he) (.base hhigh)
    exact Hilbert.Local.finish (Hilbert.Local.discharge out)
  exact ⟨.mp (.mp (.mp (.logical (.orElim _ _ _)) hleft) hright) hc⟩

theorem pairFirstBound : Targets.PairFirstBound := by
  intro n p tag ht ctx a b
  let T := GorbowPRNumeralCalculation.Theory p
  have hl : Derivation T (weakBound a (.add (.mul b b) a)) :=
    .mp (weakIntro a _ (.mul b b)) (addComm (.mul b b) a)
  have he0 := Logic.unary (.add (.var 0) (liftTerm b)) _ _ (addComm (T := T) (.mul a a) a)
  simp only [substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] at he0
  have he : Derivation T (.equal (.add (.add (.mul a a) a) b) (.add a (.add (.mul a a) b))) :=
    Logic.trans _ _ _ he0 (addAssoc a (.mul a a) b)
  have hh : Derivation T (weakBound a (.add (.add (.mul a a) a) b)) :=
    .mp (weakIntro a _ (.add (.mul a a) b)) he
  exact pairBound p tag ht a b a hl hh

theorem pairSecondBound : Targets.PairSecondBound := by
  intro n p tag ht ctx a b
  let T := GorbowPRNumeralCalculation.Theory p
  obtain ⟨happend⟩ := weakAdd T b (.mul b b) a
  have hl : Derivation T (weakBound b (.add (.mul b b) a)) := .mp happend (squareBound b)
  have hh : Derivation T (weakBound b (.add (.add (.mul a a) a) b)) :=
    .mp (weakIntro b _ (.add (.mul a a) a)) (addComm (.add (.mul a a) a) b)
  exact pairBound p tag ht a b b hl hh

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryBounds.PairProof
