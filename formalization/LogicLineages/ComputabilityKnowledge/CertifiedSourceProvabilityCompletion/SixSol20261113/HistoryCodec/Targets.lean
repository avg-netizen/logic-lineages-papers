module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCodec.Definitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCodec.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector

def NativePair : Prop := ∀ v : List.Vector Nat 2, evaluate pair v = Nat.pair v.head v.tail.head

def NativeCons : Prop := ∀ (entry : GorbowProofChecker.Entry) (tail : GorbowProofChecker.History),
  evaluate cons (Encodable.encode entry ::ᵥ Encodable.encode tail ::ᵥ nil) = Encodable.encode (entry :: tail)

def NativeConsAllVectors : Prop := ∀ v : List.Vector Nat 2,
  evaluate cons v = (Nat.pair v.head v.tail.head).succ

def InternalAdd : Prop := ∀ n (p : Program n) tag,
  (nodes p)[tag]? = some ⟨2,add⟩ → ∀ ctx (a b : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (.equal (call tag (a ::ᵥ b ::ᵥ nil)) (.add b a)))

def InternalMultiply : Prop := ∀ n (p : Program n) tag,
  (nodes p)[tag]? = some ⟨2,multiply⟩ → ∀ ctx (a b : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (.equal (call tag (a ::ᵥ b ::ᵥ nil)) (.mul b a)))

/-- The actual difference-call branch, not an externally reflected comparison. -/
def InternalPairZero : Prop := ∀ n (p : Program n) tag,
  (nodes p)[tag]? = some ⟨2,pair⟩ → ∀ ctx (a b : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (pairZeroClause tag a b))

def InternalPairPositive : Prop := ∀ n (p : Program n) tag,
  (nodes p)[tag]? = some ⟨2,pair⟩ → ∀ ctx (a b k : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (pairPositiveClause tag a b k))

/-- Symbolic existing cons codec, with the actual paired child kept explicit. -/
def InternalCons : Prop := ∀ n (p : Program n) tag,
  (nodes p)[tag]? = some ⟨2,cons⟩ → ∀ ctx (a b : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (.equal (call tag (a ::ᵥ b ::ᵥ nil))
      (.succ (call (tag + GorbowPRChildTags.argumentTag Program.succ (fun _ : Fin 1 => pair) 0)
        (a ::ᵥ b ::ᵥ nil)))))

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCodec.Targets
