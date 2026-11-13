module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorSuffix.Targets

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorSuffix.ShellSuccessorProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowSubstitution
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open HistoryBounds HistoryBounds.SupportProof HistoryCancellation.OrderSupportProof

theorem lowerInterior {n ctx : Nat} (p : Program n) tag
    (ht : (nodes p)[tag]? = some ⟨2,HistoryCodec.pair⟩) (a b : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.imp (HistoryOrder.lower a b) (.imp (HistoryOrder.lower (.succ a) b)
        (.equal (HistoryKernel.pairCall tag (.succ a) b) (.succ (HistoryKernel.pairCall tag a b)))))) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let H := HistoryOrder.lower a b
  let J := HistoryOrder.lower (.succ a) b
  obtain ⟨h0⟩ := HistoryOrder.PairProof.pairLowerOrder n p tag ht ctx a b
  obtain ⟨h1⟩ := HistoryOrder.PairProof.pairLowerOrder n p tag ht ctx (.succ a) b
  have e0 : Hilbert.Local T ctx [J,H]
      (.equal (HistoryKernel.pairCall tag a b) (.add (.mul b b) a)) :=
    .mp (.base h0) (.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))
  have e1 : Hilbert.Local T ctx [J,H]
      (.equal (HistoryKernel.pairCall tag (.succ a) b) (.add (.mul b b) (.succ a))) :=
    .mp (.base h1) (.hypothesis List.mem_cons_self)
  have e := localTrans _ _ _ e1 (.base (.arithmetic (.addSucc (.mul b b) a)))
  have es := localUnary (.succ (.var 0)) _ _ e0
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge
    (localTrans _ _ _ e (HistoryOrder.StepProof.localSym _ _ es))))⟩

theorem upperInterior {n ctx : Nat} (p : Program n) tag
    (ht : (nodes p)[tag]? = some ⟨2,HistoryCodec.pair⟩) (a b : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.imp (HistoryOrder.upper a b) (.imp (HistoryOrder.upper a (.succ b))
        (.equal (HistoryKernel.pairCall tag a (.succ b)) (.succ (HistoryKernel.pairCall tag a b)))))) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let H := HistoryOrder.upper a b
  let J := HistoryOrder.upper a (.succ b)
  obtain ⟨h0⟩ := HistoryOrder.PairProof.pairUpperOrder n p tag ht ctx a b
  obtain ⟨h1⟩ := HistoryOrder.PairProof.pairUpperOrder n p tag ht ctx a (.succ b)
  have e0 : Hilbert.Local T ctx [J,H]
      (.equal (HistoryKernel.pairCall tag a b) (.add (.add (.mul a a) a) b)) :=
    .mp (.base h0) (.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))
  have e1 : Hilbert.Local T ctx [J,H]
      (.equal (HistoryKernel.pairCall tag a (.succ b)) (.add (.add (.mul a a) a) (.succ b))) :=
    .mp (.base h1) (.hypothesis List.mem_cons_self)
  have e := localTrans _ _ _ e1 (.base (.arithmetic (.addSucc (.add (.mul a a) a) b)))
  have es := localUnary (.succ (.var 0)) _ _ e0
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge
    (localTrans _ _ _ e (HistoryOrder.StepProof.localSym _ _ es))))⟩

/-- Crossing the lower half-shell to the upper half-shell, with no premise. -/
theorem lowerBoundary {n ctx : Nat} (p : Program n) tag
    (ht : (nodes p)[tag]? = some ⟨2,HistoryCodec.pair⟩) (a : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (HistoryKernel.pairCall tag (.succ a) .zero)
        (.succ (HistoryKernel.pairCall tag a (.succ a))))) := by
  let T := GorbowPRNumeralCalculation.Theory p
  obtain ⟨hl⟩ := HistoryOrder.PairProof.pairLowerOrder n p tag ht ctx a (.succ a)
  obtain ⟨hu⟩ := HistoryOrder.PairProof.pairUpperOrder n p tag ht ctx (.succ a) .zero
  have el := Derivation.mp hl (HistoryCancellation.ShellProof.strictSuccessor (T := T) a)
  have eu := Derivation.mp hu (weakZero (T := T) (.succ a))
  have e := Logic.trans _ _ _ eu
    (Logic.trans _ _ _ (.arithmetic (.addZero _)) (.arithmetic (.addSucc (.mul (.succ a) (.succ a)) a)))
  exact ⟨Logic.trans _ _ _ e (Support.equalitySymmetry _ _ (Logic.unary (.succ (.var 0)) _ _ el))⟩

/-- Crossing the shell diagonal to the next square, with no premise. -/
theorem upperBoundary {n ctx : Nat} (p : Program n) tag
    (ht : (nodes p)[tag]? = some ⟨2,HistoryCodec.pair⟩) (a : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (HistoryKernel.pairCall tag .zero (.succ a))
        (.succ (HistoryKernel.pairCall tag a a)))) := by
  let T := GorbowPRNumeralCalculation.Theory p
  obtain ⟨hl⟩ := HistoryOrder.PairProof.pairLowerOrder n p tag ht ctx .zero (.succ a)
  obtain ⟨hu⟩ := HistoryOrder.PairProof.pairUpperOrder n p tag ht ctx a a
  have hpos : Derivation T (HistoryOrder.lower (.zero : Term ctx) (.succ a)) :=
    .mp (HistoryOrder.SupportProof.lowerIntro .zero (.succ a) a)
      (Support.equalitySymmetry _ _ (zeroLeft (.succ a)))
  have el := Derivation.mp hl hpos
  have eu := Derivation.mp hu (weakReflexive (T := T) a)
  have e := Logic.trans _ _ _ el
    (Logic.trans _ _ _ (.arithmetic (.addZero _)) (HistoryCancellation.SquareProof.squareSuccessor a))
  exact ⟨Logic.trans _ _ _ e (Support.equalitySymmetry _ _ (Logic.unary (.succ (.var 0)) _ _ eu))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorSuffix.ShellSuccessorProof
