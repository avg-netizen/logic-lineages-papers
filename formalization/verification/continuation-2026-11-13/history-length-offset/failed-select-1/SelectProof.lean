module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLengthOffset.EquationsProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLengthOffset.SelectProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport EquationsProof
open HistoryDecoder.SelectGraphProof (testCongruence)

noncomputable def countCongruence {T : Sentence → Prop} {ctx : Nat} {G : List (Formula ctx)} tag (a b c d : Term ctx)
    (hab : Hilbert.Local T ctx G (.equal a b)) (hcd : Hilbert.Local T ctx G (.equal c d)) :
    Hilbert.Local T ctx G (.equal (countCall tag a c) (countCall tag b d)) :=
  HistoryIteratorSuffix.StepSuffixProof.pairCongruence tag a c b d hab hcd

noncomputable def selectValues {T : Sentence → Prop} {ctx : Nat} {G : List (Formula ctx)} tag (test a b c d : Term ctx)
    (hab : Hilbert.Local T ctx G (.equal a b)) (hcd : Hilbert.Local T ctx G (.equal c d)) :
    Hilbert.Local T ctx G (.equal (selectCall tag test a c) (selectCall tag test b d)) := by
  have h1 := localUnary (selectCall tag (liftTerm test) (.var 0) (liftTerm c)) a b hab
  have h2 := localUnary (selectCall tag (liftTerm test) (liftTerm b) (.var 0)) c d hcd
  simp only [substSelect,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] at h1 h2
  exact localTrans _ _ _ h1 h2

def commutes {ctx : Nat} (tag : Nat) (test a b : Term ctx) : Formula ctx :=
  .equal (selectCall tag test (.succ a) (.succ b)) (.succ (selectCall tag test a b))
theorem substCommutes {m n : Nat} (sub : Fin m → Term n) tag (test a b : Term m) :
    substituteFormula sub (commutes tag test a b)=commutes tag (substitute sub test) (substitute sub a) (substitute sub b) := by
  simp only [commutes,substituteFormula,substSelect,substitute]

theorem selectSuccessor {n ctx : Nat} (p : Program n) tag
    (ht : (nodes p)[tag]? = some ⟨3,HistoryCodec.select⟩) (test a b : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (commutes tag test a b)) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let E := Formula.equal test .zero
  have he : Hilbert.Local T ctx [E] E := .hypothesis List.mem_cons_self
  obtain ⟨hl⟩ := HistoryCodec.PairProof.selectZero p tag ht (.succ a) (.succ b)
  obtain ⟨hr⟩ := HistoryCodec.PairProof.selectZero p tag ht a b
  have hleft := localTrans _ _ _ (testCongruence tag test .zero (.succ a) (.succ b) he) (.base hl)
  have hright := localTrans _ _ _ (testCongruence tag test .zero a b he) (.base hr)
  have hz : Derivation T (.imp E (commutes tag test a b)) := Hilbert.Local.finish (Hilbert.Local.discharge
    (localTrans _ _ _ hleft (HistoryOrder.StepProof.localSym _ _ (localUnary (.succ (.var 0)) _ _ hright))))
  let H := HistoryOrder.SupportProof.predBody test
  have hh : Hilbert.Local T (ctx+1) [H] (.equal (liftTerm test) (.succ (.var 0))) := .hypothesis List.mem_cons_self
  obtain ⟨hlp⟩ := HistoryCodec.PairProof.selectPositive p tag ht (.succ (liftTerm a)) (.succ (liftTerm b)) (.var (0 : Fin (ctx+1)))
  obtain ⟨hrp⟩ := HistoryCodec.PairProof.selectPositive p tag ht (liftTerm a) (liftTerm b) (.var (0 : Fin (ctx+1)))
  have hleftp := localTrans _ _ _ (testCongruence tag (liftTerm test) (.succ (.var 0)) (.succ (liftTerm a)) (.succ (liftTerm b)) hh) (.base hlp)
  have hrightp := localTrans _ _ _ (testCongruence tag (liftTerm test) (.succ (.var 0)) (liftTerm a) (liftTerm b) hh) (.base hrp)
  have hp : Derivation T (.imp H (GorbowPACore.weaken (commutes tag test a b))) := by
    simpa only [GorbowPACore.weaken,substCommutes,commutes,liftTerm,renameTerm,substitute,Fin.cases_zero] using
      Hilbert.Local.finish (Hilbert.Local.discharge
        (localTrans _ _ _ hleftp (HistoryOrder.StepProof.localSym _ _ (localUnary (.succ (.var 0)) _ _ hrightp))))
  obtain ⟨hp⟩ := HBQuantifier.existentialElimination T H (commutes tag test a b) ⟨hp⟩
  obtain ⟨hc⟩ := HistoryOrder.SupportProof.zeroOrSuccessor T test
  exact ⟨.mp (.mp (.mp (.logical (.orElim _ _ _)) hz) hp) hc⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLengthOffset.SelectProof
