module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryKernel.TransitionEquationsProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryKernel.NormalProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryRuleSuffix FieldsProof EntryProof TransitionEquationsProof

theorem testEquation {n ctx : Nat} (p : Program n) tag ptag ctag (v l a : Program 1) (x : Program 3)
    (ht : (nodes p)[tag]? = some ⟨3,kernel v l a x⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (index fuel h line rest : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call (testTag tag v l a x) (activeArgs ptag ctag index fuel h line rest))
        (pairCall (equalityTag tag v l a x)
          (HistoryDispatcher.dispatcherCall (dispatcherTag tag v l a x) index fuel h line) (.succ .zero)))) := by
  have htest := testInstalled p tag v l a x ht
  exact HistoryAppend.ValueEquationsProof.binaryValues p (testTag tag v l a x) equalCode (testArguments v l a x) htest _ _ _
    (checkedEquation p (checkTag tag v l a x) ptag ctag v l a x (checkInstalled p tag v l a x ht) hp hc index fuel h line rest)
    (EqualEquationsProof.oneEquation p _
      (SixSol20261112.Fuel.Equations.argumentChild p (testTag tag v l a x) equalCode (testArguments v l a x) htest 1) _)

theorem acceptedEquation {n ctx : Nat} (p : Program n) tag ptag ctag (v l a : Program 1) (x : Program 3)
    (ht : (nodes p)[tag]? = some ⟨3,kernel v l a x⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (index fuel h line rest : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call (acceptedTag tag v l a x) (activeArgs ptag ctag index fuel h line rest))
        (optionValue tag v l a x index fuel h line))) := by
  have hacc := acceptedInstalled p tag v l a x ht
  exact threeValues p (acceptedTag tag v l a x) HistoryCodec.select (acceptedArguments v l a x) hacc _ _ _ _
    (testEquation p tag ptag ctag v l a x ht hp hc index fuel h line rest)
    (HistoryAppend.TableEquationsProof.zeroEquation p _
      (SixSol20261112.Fuel.Equations.argumentChild p (acceptedTag tag v l a x) HistoryCodec.select (acceptedArguments v l a x) hacc 1) _)
    (someEquation p (someTag tag v l a x) ptag ctag (someInstalled p tag v l a x ht) hp hc index fuel h line rest)

theorem optionEquation {n ctx : Nat} (p : Program n) tag ptag ctag (v l a : Program 1) (x : Program 3)
    (ht : (nodes p)[tag]? = some ⟨3,kernel v l a x⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (index fuel h line rest : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call (optionTag tag v l a x) (activeArgs ptag ctag index fuel h line rest))
        (optionValue tag v l a x index fuel h line))) := by
  have hopt := optionInstalled p tag v l a x ht
  obtain ⟨he⟩ := threeValues p (optionTag tag v l a x) HistoryCodec.select (optionArguments v l a x) hopt
    (activeArgs ptag ctag index fuel h line rest) (.succ h) .zero (optionValue tag v l a x index fuel h line)
    (FieldsProof.optionEquation p _ ptag ctag
      (SixSol20261112.Fuel.Equations.argumentChild p (optionTag tag v l a x) HistoryCodec.select (optionArguments v l a x) hopt 0) hp index fuel h line rest)
    (HistoryAppend.TableEquationsProof.zeroEquation p _
      (SixSol20261112.Fuel.Equations.argumentChild p (optionTag tag v l a x) HistoryCodec.select (optionArguments v l a x) hopt 1) _)
    (acceptedEquation p tag ptag ctag v l a x ht hp hc index fuel h line rest)
  obtain ⟨hs⟩ := HistoryCodec.PairProof.selectPositive p (optionTag tag v l a x+1)
    (SixSol20261112.Fuel.Equations.functionChild p (optionTag tag v l a x) HistoryCodec.select (optionArguments v l a x) hopt)
    (.zero : Term ctx) (optionValue tag v l a x index fuel h line) h
  exact ⟨Logic.trans _ _ _ he hs⟩

theorem nextEquation {n ctx : Nat} (p : Program n) tag ptag ctag (v l a : Program 1) (x : Program 3)
    (ht : (nodes p)[tag]? = some ⟨3,kernel v l a x⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (index fuel h line rest : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call (nextTag tag v l a x) (activeArgs ptag ctag index fuel h line rest))
        (normal tag v l a x index fuel h line rest))) := by
  have hn := nextInstalled p tag v l a x ht
  exact HistoryAppend.ValueEquationsProof.binaryValues p (nextTag tag v l a x) HistoryCodec.pair (nextArguments v l a x) hn _ _ _
    (optionEquation p tag ptag ctag v l a x ht hp hc index fuel h line rest)
    (remainingEquation p _ ptag ctag
      (SixSol20261112.Fuel.Equations.argumentChild p (nextTag tag v l a x) HistoryCodec.pair (nextArguments v l a x) hn 1) hp hc index fuel h line rest)

theorem selectOnCons {n ctx : Nat} (p : Program n) tag ctag
    (ht : (nodes p)[tag]? = some ⟨3,HistoryCodec.select⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (line rest yes no : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call tag (HistoryLookup.consCall ctag line rest ::ᵥ yes ::ᵥ no ::ᵥ nil)) no)) := by
  obtain ⟨he⟩ := HistoryCodec.PairProof.internalCons n p ctag hc ctx line rest
  have changeTest := HistoryDecoder.SelectGraphProof.testCongruence (G := []) tag
    (HistoryLookup.consCall ctag line rest) (.succ (pairCall (ctag+argumentTag .succ (fun _ : Fin 1 => HistoryCodec.pair) 0) line rest)) yes no (.base he)
  obtain ⟨hs⟩ := HistoryCodec.PairProof.selectPositive p tag ht yes no (pairCall (ctag+argumentTag .succ (fun _ : Fin 1 => HistoryCodec.pair) 0) line rest)
  exact ⟨Logic.trans _ _ _ (Hilbert.Local.finish changeTest) hs⟩

theorem kernelEquation {n ctx : Nat} (p : Program n) tag ptag ctag (v l a : Program 1) (x : Program 3)
    (ht : (nodes p)[tag]? = some ⟨3,kernel v l a x⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (index fuel h line rest : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (kernelCall tag (activeState ptag ctag h line rest) index fuel)
        (normal tag v l a x index fuel h line rest))) := by
  obtain ⟨he⟩ := threeValues p tag HistoryCodec.select (kernelArguments v l a x) ht
    (activeArgs ptag ctag index fuel h line rest) (HistoryLookup.consCall ctag line rest)
    (activeState ptag ctag h line rest) (normal tag v l a x index fuel h line rest)
    (linesEquation p _ ptag ctag
      (SixSol20261112.Fuel.Equations.argumentChild p tag HistoryCodec.select (kernelArguments v l a x) ht 0) hp index fuel h line rest)
    (SixSol20261112.Fuel.Equations.projection p _ (0 : Fin 3)
      (SixSol20261112.Fuel.Equations.argumentChild p tag HistoryCodec.select (kernelArguments v l a x) ht 1) _)
    (nextEquation p tag ptag ctag v l a x ht hp hc index fuel h line rest)
  obtain ⟨hs⟩ := selectOnCons p (tag+1) ctag
    (SixSol20261112.Fuel.Equations.functionChild p tag HistoryCodec.select (kernelArguments v l a x) ht) hc
    line rest (activeState ptag ctag h line rest) (normal tag v l a x index fuel h line rest)
  exact ⟨Logic.trans _ _ _ he hs⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryKernel.NormalProof
