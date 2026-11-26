module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLookup.Definitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLookup.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector

/-- Calibrated to the ORIGINAL checker History and getElem?, including none.
This native result is not reflected into the internal source derivations. -/
def NativeHistoryLookup : Prop := ∀ (index : Nat) (history : GorbowProofChecker.History),
  evaluate lookup (index ::ᵥ Encodable.encode history ::ᵥ nil) = Encodable.encode (history[index]?)

/-- Cons may live at any actual registry address, not just a destructor child. -/
def InternalHeadCons : Prop := ∀ n (p : Program n) headTag consTag,
  (nodes p)[headTag]? = some ⟨1,head⟩ →
  (nodes p)[consTag]? = some ⟨2,HistoryCodec.cons⟩ → ∀ ctx (a b : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (.equal (call headTag (consCall consTag a b ::ᵥ nil)) a))
def InternalTailCons : Prop := ∀ n (p : Program n) tailTag consTag,
  (nodes p)[tailTag]? = some ⟨1,tail⟩ →
  (nodes p)[consTag]? = some ⟨2,HistoryCodec.cons⟩ → ∀ ctx (a b : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (.equal (call tailTag (consCall consTag a b ::ᵥ nil)) b))

/-- Index zero returns encoded SOME, not a zero-default payload. -/
def InternalLookupZeroCons : Prop := ∀ n (p : Program n) lookupTag consTag,
  (nodes p)[lookupTag]? = some ⟨2,lookup⟩ →
  (nodes p)[consTag]? = some ⟨2,HistoryCodec.cons⟩ → ∀ ctx (a b : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (.equal (lookupCall lookupTag .zero (consCall consTag a b)) (.succ a)))
def InternalLookupSuccessorCons : Prop := ∀ n (p : Program n) lookupTag consTag,
  (nodes p)[lookupTag]? = some ⟨2,lookup⟩ →
  (nodes p)[consTag]? = some ⟨2,HistoryCodec.cons⟩ → ∀ ctx (index a b : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (.equal (lookupCall lookupTag (.succ index) (consCall consTag a b))
      (lookupCall lookupTag index b)))

/-- Missing reference remains encoded NONE for every index. -/
def InternalLookupNil : Prop := ∀ n (p : Program n) lookupTag,
  (nodes p)[lookupTag]? = some ⟨2,lookup⟩ → ∀ ctx (index : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (.equal (lookupCall lookupTag index .zero) .zero))

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLookup.Targets
