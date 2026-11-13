module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCancellation.TransitivityProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCancellation.MonotonicityProof
open GorbowSyntax GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open HistoryBounds HistoryBounds.SupportProof HistoryBounds.PairProof

theorem weakAddLeft (T : Sentence → Prop) {ctx : Nat} (a b c : Term ctx) :
    Nonempty (Derivation T (.imp (weakBound a b) (weakBound (.add c a) (.add c b)))) := by
  let H := HistoryOrder.upperBody b a
  have hh : Hilbert.Local T (ctx+1) [H]
      (.equal (liftTerm b) (.add (liftTerm a) (.var 0))) := .hypothesis List.mem_cons_self
  have hc := localUnary (.add (liftTerm (liftTerm c)) (.var 0)) _ _ hh
  simp only [substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] at hc
  have he := localTrans _ _ _ hc (.base (Support.equalitySymmetry _ _
    (addAssoc (T := T) (liftTerm c) (liftTerm a) (.var 0))))
  have hout : Hilbert.Local T (ctx+1) [H]
      (weakBound (.add (liftTerm c) (liftTerm a)) (.add (liftTerm c) (liftTerm b))) :=
    .mp (.base (weakIntro _ _ (.var 0))) he
  have hbody : Derivation T (.imp H (GorbowPACore.weaken (weakBound (.add c a) (.add c b)))) := by
    simpa only [weakenWeak,liftTerm,renameTerm,substitute] using
      Hilbert.Local.finish (Hilbert.Local.discharge hout)
  exact HBQuantifier.existentialElimination T H (weakBound (.add c a) (.add c b)) ⟨hbody⟩

theorem weakChildAt {ctx : Nat} (child code : Term ctx) :
    GorbowStandardInstances.instantiate (weakBound (.var 0) (liftTerm code)) child =
      weakBound child code := by
  simp only [GorbowStandardInstances.instantiate,substWeak,substitute,
    liftTerm,Support.shiftCancel,Fin.cases_zero]

noncomputable def weakChildTransport {T : Sentence → Prop} {ctx : Nat} (child value code : Term ctx) :
    Derivation T (.imp (.equal child value) (.imp (weakBound value code) (weakBound child code))) := by
  have hr := Derivation.logical (A := T)
    (.equalityReplace (weakBound (.var 0) (liftTerm code)) value child)
  rw [GorbowPACore.logicalFormula,weakChildAt,weakChildAt] at hr
  exact Hilbert.compose hr (Logic.symmetryRule T child value)

theorem strictAddLeft (T : Sentence → Prop) {ctx : Nat} (a b c : Term ctx) :
    Nonempty (Derivation T (.imp (strictBound a b) (strictBound (.add c a) (.add c b)))) := by
  let H := HistoryOrder.lowerBody a b
  have hh : Hilbert.Local T (ctx+1) [H]
      (.equal (liftTerm b) (.add (liftTerm a) (.succ (.var 0)))) := .hypothesis List.mem_cons_self
  have hc := localUnary (.add (liftTerm (liftTerm c)) (.var 0)) _ _ hh
  simp only [substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] at hc
  have he := localTrans _ _ _ hc (.base (Support.equalitySymmetry _ _
    (addAssoc (T := T) (liftTerm c) (liftTerm a) (.succ (.var 0)))))
  have hout : Hilbert.Local T (ctx+1) [H]
      (strictBound (.add (liftTerm c) (liftTerm a)) (.add (liftTerm c) (liftTerm b))) :=
    .mp (.base (strictIntro _ _ (.var 0))) he
  have hbody : Derivation T (.imp H (GorbowPACore.weaken (strictBound (.add c a) (.add c b)))) := by
    simpa only [weakenStrict,liftTerm,renameTerm,substitute] using
      Hilbert.Local.finish (Hilbert.Local.discharge hout)
  exact HBQuantifier.existentialElimination T H (strictBound (.add c a) (.add c b)) ⟨hbody⟩

theorem strictChildAt {ctx : Nat} (child code : Term ctx) :
    GorbowStandardInstances.instantiate (strictBound (.var 0) (liftTerm code)) child =
      strictBound child code := by
  simp only [GorbowStandardInstances.instantiate,substStrict,substitute,
    liftTerm,Support.shiftCancel,Fin.cases_zero]

noncomputable def strictChildTransport {T : Sentence → Prop} {ctx : Nat} (child value code : Term ctx) :
    Derivation T (.imp (.equal child value) (.imp (strictBound value code) (strictBound child code))) := by
  have hr := Derivation.logical (A := T)
    (.equalityReplace (strictBound (.var 0) (liftTerm code)) value child)
  rw [GorbowPACore.logicalFormula,strictChildAt,strictChildAt] at hr
  exact Hilbert.compose hr (Logic.symmetryRule T child value)

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCancellation.MonotonicityProof
