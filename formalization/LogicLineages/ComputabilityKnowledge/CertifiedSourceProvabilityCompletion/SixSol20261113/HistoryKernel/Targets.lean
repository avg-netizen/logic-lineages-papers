module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryKernel.Definitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryKernel.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector

/-- Every raw code actually encodes an original State. This supplier must be
constructed from the actual codecs, not postulated to erase default behavior. -/
def StateCodecTotal : Prop := ∀ code : Nat,
  ∃ state : SixSol20261112.HistoryMachine.State, Encodable.encode state=code

/-- Exact old kernelFunction on ALL vectors, including decodedState/default
behavior. The actual literal kernel is newly chosen, never asserted equal as
an AST to the old opaque existential witness. -/
def NativeKernel : Prop := ∀ (valid logical arithmetic : Program 1) (axiomProgram : Program 3),
  HistoryDispatcher.NativeLeaves valid logical arithmetic axiomProgram →
  SixSol20261112.HistoryMachine.KernelProgram (kernel valid logical arithmetic axiomProgram)

/-- Internal actual equality guard soundness. No native reflection or assumed
Boolean range for the compared terms. -/
def InternalEqualSound : Prop := ∀ arity (p : Program arity) tag,
  (nodes p)[tag]? = some ⟨2,HistoryRuleSuffix.equalCode⟩ → ∀ ctx (a b : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (.imp (.equal (pairCall tag a b) (.succ .zero)) (.equal a b)))

def InternalEqualComplete : Prop := ∀ arity (p : Program arity) tag,
  (nodes p)[tag]? = some ⟨2,HistoryRuleSuffix.equalCode⟩ → ∀ ctx (a b : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (.imp (.equal a b) (.equal (pairCall tag a b) (.succ .zero))))

/-- Actual original successful-step suffix closure, every source term.
The only logical premise is the actual old kernel step returning SOME out.
All four calls use actual installed AST addresses; no state reconstruction,
line validity, reference bounds or native leaf calibration is assumed. -/
def InternalStepSuffix : Prop := ∀ (valid logical arithmetic : Program 1) (axiomProgram : Program 3),
  ∀ arity (p : Program arity) ktag atag ptag ctag,
  (nodes p)[ktag]? = some ⟨3,kernel valid logical arithmetic axiomProgram⟩ →
  (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
  (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
  (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
  ∀ ctx (index fuel h tail line rest out : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (stepSuffix ktag atag ptag ctag index fuel h tail line rest out))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryKernel.Targets
