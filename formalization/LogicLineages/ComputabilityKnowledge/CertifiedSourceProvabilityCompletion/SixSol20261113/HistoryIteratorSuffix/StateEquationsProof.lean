module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorSuffix.Targets

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorSuffix.StateEquationsProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryKernel HistoryKernel.TransitionEquationsProof

def args {ctx : Nat} (ptag : Nat) (option lines index fuel : Term ctx) : List.Vector (Term ctx) 3 :=
  pairCall ptag option lines ::ᵥ index ::ᵥ fuel ::ᵥ nil

theorem field {n ctx : Nat} (p : Program n) tag ptag right
    (ht : (nodes p)[tag]? = some ⟨3,HistoryRuleSuffix.applyOne (HistoryDecoder.decoder right) (.projection 0)⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩) (option lines index fuel : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call tag (args ptag option lines index fuel))
        (HistoryDecoder.StepNormalProof.chosen right option lines))) := by
  have hd := Equations.functionChild p tag (HistoryDecoder.decoder right) (fun _ : Fin 1 => .projection (0 : Fin 3)) ht
  have hv := Equations.argumentChild p tag (HistoryDecoder.decoder right) (fun _ : Fin 1 => .projection (0 : Fin 3)) ht 0
  obtain ⟨he⟩ := HistoryAppend.ValueEquationsProof.unaryValues p tag (HistoryDecoder.decoder right) _ ht
    (args ptag option lines index fuel) (pairCall ptag option lines)
    (Equations.projection p _ (0 : Fin 3) hv _)
  obtain ⟨hc⟩ := HistoryLookup.DestructorProof.decoderCrossPair p (tag+1) ptag right hd hp option lines
  exact ⟨Logic.trans _ _ _ he hc⟩

/-- The literal kernel stutters on nil for arbitrary Option payload. -/
theorem kernelNil {n ctx : Nat} (p : Program n) tag ptag (v l a : Program 1) (x : Program 3)
    (ht : (nodes p)[tag]? = some ⟨3,kernel v l a x⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩) (option index fuel : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (kernelCall tag (pairCall ptag option .zero) index fuel) (pairCall ptag option .zero))) := by
  let av := args ptag option .zero index fuel
  let raw := call (nextTag tag v l a x) av
  obtain ⟨he⟩ := threeValues p tag HistoryCodec.select (kernelArguments v l a x) ht av
    .zero (pairCall ptag option .zero) raw
    (field p _ ptag true (Equations.argumentChild p tag HistoryCodec.select (kernelArguments v l a x) ht 0) hp option .zero index fuel)
    (Equations.projection p _ (0 : Fin 3) (Equations.argumentChild p tag HistoryCodec.select (kernelArguments v l a x) ht 1) av)
    ⟨.logical (.reflexive _)⟩
  obtain ⟨hs⟩ := HistoryCodec.PairProof.selectZero p (tag+1)
    (Equations.functionChild p tag HistoryCodec.select (kernelArguments v l a x) ht) (pairCall ptag option .zero) raw
  exact ⟨Logic.trans _ _ _ he hs⟩

theorem remainingCons {n ctx : Nat} (p : Program n) tag ptag ctag
    (ht : (nodes p)[tag]? = some ⟨3,remainingLines⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (option line rest index fuel : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call tag (args ptag option (HistoryLookup.consCall ctag line rest) index fuel)) rest)) := by
  have hs := Equations.argumentChild p tag HistoryLookup.tail (fun _ : Fin 1 => stateLines) ht 0
  have hh := Equations.functionChild p tag HistoryLookup.tail (fun _ : Fin 1 => stateLines) ht
  obtain ⟨he⟩ := HistoryAppend.ValueEquationsProof.unaryValues p tag HistoryLookup.tail _ ht _
    (HistoryLookup.consCall ctag line rest) (field p _ ptag true hs hp option _ index fuel)
  obtain ⟨hv⟩ := HistoryLookup.DestructorProof.internalTailCons n p (tag+1) ctag hh hc ctx line rest
  exact ⟨Logic.trans _ _ _ he hv⟩

/-- The NONE guard discards the actual accepted-branch value without assuming its range. -/
theorem optionNone {n ctx : Nat} (p : Program n) tag ptag (v l a : Program 1) (x : Program 3)
    (ht : (nodes p)[tag]? = some ⟨3,kernel v l a x⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩) (lines index fuel : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call (optionTag tag v l a x) (args ptag .zero lines index fuel)) .zero)) := by
  let av := args ptag .zero lines index fuel
  let raw := call (acceptedTag tag v l a x) av
  have ho := optionInstalled p tag v l a x ht
  obtain ⟨he⟩ := threeValues p (optionTag tag v l a x) HistoryCodec.select (optionArguments v l a x) ho av
    .zero .zero raw
    (field p _ ptag false (Equations.argumentChild p _ HistoryCodec.select (optionArguments v l a x) ho 0) hp .zero lines index fuel)
    (HistoryAppend.TableEquationsProof.zeroEquation p _ (Equations.argumentChild p _ HistoryCodec.select (optionArguments v l a x) ho 1) av)
    ⟨.logical (.reflexive _)⟩
  obtain ⟨hs⟩ := HistoryCodec.PairProof.selectZero p (optionTag tag v l a x+1)
    (Equations.functionChild p _ HistoryCodec.select (optionArguments v l a x) ho) (.zero : Term ctx) raw
  exact ⟨Logic.trans _ _ _ he hs⟩

theorem kernelNoneCons {n ctx : Nat} (p : Program n) tag ptag ctag (v l a : Program 1) (x : Program 3)
    (ht : (nodes p)[tag]? = some ⟨3,kernel v l a x⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (line rest index fuel : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (kernelCall tag (pairCall ptag .zero (HistoryLookup.consCall ctag line rest)) index fuel)
        (pairCall ptag .zero rest))) := by
  let av := args ptag .zero (HistoryLookup.consCall ctag line rest) index fuel
  have hn := nextInstalled p tag v l a x ht
  obtain ⟨en⟩ := HistoryAppend.ValueEquationsProof.binaryValues p (nextTag tag v l a x) HistoryCodec.pair (nextArguments v l a x) hn av .zero rest
    (optionNone p tag ptag v l a x ht hp _ index fuel)
    (remainingCons p _ ptag ctag (Equations.argumentChild p _ HistoryCodec.pair (nextArguments v l a x) hn 1) hp hc .zero line rest index fuel)
  obtain ⟨ep⟩ := HistoryDecoder.PairCongruenceProof.pairCopies p (nextTag tag v l a x+1) ptag
    (Equations.functionChild p _ HistoryCodec.pair (nextArguments v l a x) hn) hp (.zero : Term ctx) rest
  obtain ⟨he⟩ := threeValues p tag HistoryCodec.select (kernelArguments v l a x) ht av
    (HistoryLookup.consCall ctag line rest) (pairCall ptag .zero (HistoryLookup.consCall ctag line rest)) (pairCall ptag .zero rest)
    (field p _ ptag true (Equations.argumentChild p tag HistoryCodec.select (kernelArguments v l a x) ht 0) hp .zero _ index fuel)
    (Equations.projection p _ (0 : Fin 3) (Equations.argumentChild p tag HistoryCodec.select (kernelArguments v l a x) ht 1) av)
    ⟨Logic.trans _ _ _ en ep⟩
  obtain ⟨hs⟩ := HistoryKernel.NormalProof.selectOnCons p (tag+1) ctag
    (Equations.functionChild p tag HistoryCodec.select (kernelArguments v l a x) ht) hc line rest _ _
  exact ⟨Logic.trans _ _ _ he hs⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorSuffix.StateEquationsProof
