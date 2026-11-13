module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCancellation.ArithmeticProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCancellation.OrderSupportProof
open GorbowSyntax GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport HistoryBounds HistoryBounds.SupportProof

noncomputable def positiveGapImpossible {T : Sentence → Prop} {ctx : Nat} (a k : Term ctx) :
    Derivation T (.neg (.equal a (.add a (.succ k)))) := by
  let E := Formula.equal a (.add a (.succ k))
  have he : Hilbert.Local T ctx [E] E := .hypothesis List.mem_cons_self
  have hsum := localTrans _ _ _ (.base (.arithmetic (.addZero a))) he
  have hz : Hilbert.Local T ctx [E] (.equal .zero (.succ k)) :=
    .mp (.base (ArithmeticProof.left .zero (.succ k) a)) hsum
  have hs := HistoryOrder.StepProof.localSym _ _ hz
  exact Hilbert.modusTollens (Hilbert.Local.finish (Hilbert.Local.discharge hs))
    (.arithmetic (.succNotZero k))

theorem strictIrreflexive (T : Sentence → Prop) {ctx : Nat} (a : Term ctx) :
    Nonempty (Derivation T (.neg (strictBound a a))) := by
  let H := HistoryOrder.lowerBody a a
  let F : Formula ctx := .equal (.succ .zero) .zero
  have he : Hilbert.Local T (ctx+1) [H] H := .hypothesis List.mem_cons_self
  have hf : Hilbert.Local T (ctx+1) [H] (GorbowPACore.weaken F) :=
    Hilbert.Local.explosion _ he (.base (positiveGapImpossible (liftTerm a) (.var 0)))
  obtain ⟨h⟩ := HBQuantifier.existentialElimination T H F
    ⟨Hilbert.Local.finish (Hilbert.Local.discharge hf)⟩
  exact ⟨Hilbert.modusTollens h (.arithmetic (.succNotZero .zero))⟩

noncomputable def weakReflexive {T : Sentence → Prop} {ctx : Nat} (a : Term ctx) :
    Derivation T (weakBound a a) :=
  .mp (weakIntro a a .zero) (Support.equalitySymmetry _ _ (.arithmetic (.addZero a)))

noncomputable def weakZero {T : Sentence → Prop} {ctx : Nat} (a : Term ctx) :
    Derivation T (weakBound .zero a) :=
  .mp (weakIntro .zero a a) (Support.equalitySymmetry _ _ (zeroLeft a))

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCancellation.OrderSupportProof
