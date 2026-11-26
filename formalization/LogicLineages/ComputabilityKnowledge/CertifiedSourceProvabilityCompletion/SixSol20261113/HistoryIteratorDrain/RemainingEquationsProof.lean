module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorDrain.Targets

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorDrain.RemainingEquationsProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryKernel HistoryKernel.TransitionEquationsProof
open HistoryIteratorSuffix.StateEquationsProof

def decoded {ctx : Nat} (dtag : Nat) (state : Term ctx) : Term ctx := call dtag (state ::ᵥ nil)

theorem kernelCons {n ctx : Nat} (p : Program n) (tag dtag ptag ctag : Nat) (v l a : Program 1) (x : Program 3)
    (ht : (nodes p)[tag]? = some ⟨3,kernel v l a x⟩)
    (hd : (nodes p)[dtag]? = some ⟨1,HistoryDecoder.decoder true⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (option line rest index fuel : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (decoded dtag (kernelCall tag (pairCall ptag option (HistoryLookup.consCall ctag line rest)) index fuel)) rest)) := by
  let av := args ptag option (HistoryLookup.consCall ctag line rest) index fuel
  let raw := call (optionTag tag v l a x) av
  have hn := nextInstalled p tag v l a x ht
  have hop := Equations.functionChild p (nextTag tag v l a x) HistoryCodec.pair (nextArguments v l a x) hn
  obtain ⟨en⟩ := HistoryAppend.ValueEquationsProof.binaryValues p (nextTag tag v l a x) HistoryCodec.pair (nextArguments v l a x) hn av raw rest
    ⟨.logical (.reflexive _)⟩
    (remainingCons p _ ptag ctag (Equations.argumentChild p _ HistoryCodec.pair (nextArguments v l a x) hn 1) hp hc option line rest index fuel)
  obtain ⟨he⟩ := threeValues p tag HistoryCodec.select (kernelArguments v l a x) ht av
    (HistoryLookup.consCall ctag line rest) (pairCall ptag option (HistoryLookup.consCall ctag line rest))
    (pairCall (outputPairTag tag v l a x) raw rest)
    (field p _ ptag true (Equations.argumentChild p tag HistoryCodec.select (kernelArguments v l a x) ht 0) hp option _ index fuel)
    (Equations.projection p _ (0 : Fin 3) (Equations.argumentChild p tag HistoryCodec.select (kernelArguments v l a x) ht 1) av)
    ⟨en⟩
  obtain ⟨hs⟩ := HistoryKernel.NormalProof.selectOnCons p (tag+1) ctag
    (Equations.functionChild p tag HistoryCodec.select (kernelArguments v l a x) ht) hc line rest _ _
  obtain ⟨hi⟩ := HistoryLookup.DestructorProof.decoderCrossPair p dtag (outputPairTag tag v l a x) true hd hop raw rest
  exact ⟨Logic.trans _ _ _
    (HistoryLookup.DestructorProof.unaryCallCongruence dtag _ _ (Logic.trans _ _ _ he hs)) hi⟩

theorem kernelNil {n ctx : Nat} (p : Program n) (tag dtag ptag : Nat) (v l a : Program 1) (x : Program 3)
    (ht : (nodes p)[tag]? = some ⟨3,kernel v l a x⟩)
    (hd : (nodes p)[dtag]? = some ⟨1,HistoryDecoder.decoder true⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩) (option index fuel : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (decoded dtag (kernelCall tag (pairCall ptag option .zero) index fuel)) .zero)) := by
  obtain ⟨he⟩ := HistoryIteratorSuffix.StateEquationsProof.kernelNil p tag ptag v l a x ht hp option index fuel
  obtain ⟨hi⟩ := HistoryLookup.DestructorProof.decoderCrossPair p dtag ptag true hd hp option (.zero : Term ctx)
  exact ⟨Logic.trans _ _ _ (HistoryLookup.DestructorProof.unaryCallCongruence dtag _ _ he) hi⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorDrain.RemainingEquationsProof
