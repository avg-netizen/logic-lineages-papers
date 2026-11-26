module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryKernel.NormalProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryKernel.RangeProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryKernel.OptionProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open FieldsProof EntryProof TransitionEquationsProof

theorem kernelNodes {n : Nat} (p : Program n) tag (v l a : Program 1) (x : Program 3)
    (ht : (nodes p)[tag]? = some ⟨3,kernel v l a x⟩) :
    (nodes p)[outputPairTag tag v l a x]? = some ⟨2,HistoryCodec.pair⟩ ∧
    (nodes p)[selectorTag tag v l a x]? = some ⟨3,HistoryCodec.select⟩ ∧
    (nodes p)[equalityTag tag v l a x]? = some ⟨2,HistoryRuleSuffix.equalCode⟩ ∧
    (nodes p)[dispatcherTag tag v l a x]? = some ⟨4,HistoryDispatcher.lineDispatcher v l a x⟩ ∧
    (nodes p)[outputConsTag (someTag tag v l a x)]? = some ⟨2,HistoryCodec.cons⟩ := by
  exact ⟨SixSol20261112.Fuel.Equations.functionChild p _ HistoryCodec.pair (nextArguments v l a x) (nextInstalled p tag v l a x ht),
    SixSol20261112.Fuel.Equations.functionChild p _ HistoryCodec.select (acceptedArguments v l a x) (acceptedInstalled p tag v l a x ht),
    SixSol20261112.Fuel.Equations.functionChild p _ HistoryRuleSuffix.equalCode (testArguments v l a x) (testInstalled p tag v l a x ht),
    SixSol20261112.Fuel.Equations.functionChild p _ (HistoryDispatcher.lineDispatcher v l a x) dispatcherArguments (checkInstalled p tag v l a x ht),
    outputConsInstalled p _ (someInstalled p tag v l a x ht)⟩

theorem optionGraph {n ctx : Nat} (p : Program n) tag (v l a : Program 1) (x : Program 3)
    (ht : (nodes p)[tag]? = some ⟨3,kernel v l a x⟩) (index fuel h line : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.disj (.equal (optionValue tag v l a x index fuel h line) .zero)
        (.conj (.equal (HistoryDispatcher.dispatcherCall (dispatcherTag tag v l a x) index fuel h line) (.succ .zero))
          (.equal (optionValue tag v l a x index fuel h line) (.succ (newHistory (someTag tag v l a x) h line)))))) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let C := HistoryDispatcher.dispatcherCall (dispatcherTag tag v l a x) index fuel h line
  let K := pairCall (equalityTag tag v l a x) C (.succ .zero)
  let N := newHistory (someTag tag v l a x) h line
  let O := optionValue tag v l a x index fuel h line
  let Q := Formula.disj (.equal O .zero) (.conj (.equal C (.succ .zero)) (.equal O (.succ N)))
  obtain ⟨hp,hs,he,hd,hc⟩ := kernelNodes p tag v l a x ht
  obtain ⟨hr⟩ := RangeProof.equalRange p (equalityTag tag v l a x) he C (.succ .zero)
  obtain ⟨hz⟩ := HistoryCodec.PairProof.selectZero p (selectorTag tag v l a x) hs (.zero : Term ctx) (.succ N)
  obtain ⟨ho⟩ := HistoryCodec.PairProof.selectPositive p (selectorTag tag v l a x) hs (.zero : Term ctx) (.succ N) .zero
  obtain ⟨sound⟩ := EqualProof.internalEqualSound n p (equalityTag tag v l a x) he ctx C (.succ .zero)
  have hzero : Derivation T (.imp (.equal K .zero) Q) := by
    have e : Hilbert.Local T ctx [.equal K .zero] (.equal K .zero) := .hypothesis List.mem_cons_self
    have hc := HistoryDecoder.SelectGraphProof.testCongruence (selectorTag tag v l a x) K .zero .zero (.succ N) e
    exact Hilbert.Local.finish (Hilbert.Local.discharge
      (.mp (.base (.logical (.orLeft _ _))) (localTrans _ _ _ hc (.base hz))))
  have hone : Derivation T (.imp (.equal K (.succ .zero)) Q) := by
    have e : Hilbert.Local T ctx [.equal K (.succ .zero)] (.equal K (.succ .zero)) := .hypothesis List.mem_cons_self
    have hc := HistoryDecoder.SelectGraphProof.testCongruence (selectorTag tag v l a x) K (.succ .zero) .zero (.succ N) e
    have hcheck := Hilbert.Local.mp (.base sound) e
    have hvalue := localTrans _ _ _ hc (.base ho)
    exact Hilbert.Local.finish (Hilbert.Local.discharge
      (.mp (.base (.logical (.orRight _ _))) (.mp (.mp (.base (.logical (.andIntro _ _))) hcheck) hvalue)))
  exact ⟨.mp (.mp (.mp (.logical (.orElim _ _ _)) hzero) hone) hr⟩

theorem optionAccepted {n ctx : Nat} (p : Program n) tag (v l a : Program 1) (x : Program 3)
    (ht : (nodes p)[tag]? = some ⟨3,kernel v l a x⟩) (index fuel h line : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.imp (.equal (HistoryDispatcher.dispatcherCall (dispatcherTag tag v l a x) index fuel h line) (.succ .zero))
        (.equal (optionValue tag v l a x index fuel h line) (.succ (newHistory (someTag tag v l a x) h line))))) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let C := HistoryDispatcher.dispatcherCall (dispatcherTag tag v l a x) index fuel h line
  let K := pairCall (equalityTag tag v l a x) C (.succ .zero)
  let N := newHistory (someTag tag v l a x) h line
  let E := Formula.equal C (.succ .zero)
  obtain ⟨hp,hs,he,hd,hc⟩ := kernelNodes p tag v l a x ht
  obtain ⟨complete⟩ := EqualProof.internalEqualComplete n p (equalityTag tag v l a x) he ctx C (.succ .zero)
  obtain ⟨ho⟩ := HistoryCodec.PairProof.selectPositive p (selectorTag tag v l a x) hs (.zero : Term ctx) (.succ N) .zero
  have e : Hilbert.Local T ctx [E] E := .hypothesis List.mem_cons_self
  have eqtest := Hilbert.Local.mp (.base complete) e
  have hc := HistoryDecoder.SelectGraphProof.testCongruence (selectorTag tag v l a x) K (.succ .zero) .zero (.succ N) eqtest
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (localTrans _ _ _ hc (.base ho)))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryKernel.OptionProof
