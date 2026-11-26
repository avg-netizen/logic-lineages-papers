module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryAppend.Definitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryAppend.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector

/-- Exact original newest-first History append, not a surrogate list codec. -/
def NativeHistoryAppend : Prop := ∀ (left right : GorbowProofChecker.History),
  evaluate append (Encodable.encode left ::ᵥ Encodable.encode right ::ᵥ nil) = Encodable.encode (left ++ right)

def InternalAppendNil : Prop := ∀ n (p : Program n) tag,
  (nodes p)[tag]? = some ⟨2,append⟩ → ∀ ctx (right : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (appendCall tag .zero right) right))

/-- Runtime recursion law at arbitrary actual cons addresses and source terms. -/
def InternalAppendCons : Prop := ∀ n (p : Program n) tag consTag,
  (nodes p)[tag]? = some ⟨2,append⟩ → (nodes p)[consTag]? = some ⟨2,HistoryCodec.cons⟩ →
  ∀ ctx (a left right : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (.equal (appendCall tag (HistoryLookup.consCall consTag a left) right)
      (HistoryLookup.consCall consTag a (appendCall tag left right))))

/-- The actual successful-reference preservation needed by original
line_suffix for rule2/rule3. Scope: arbitrary source terms, with successful
Option-encoded lookup as the ONLY validity premise. There is no assumed coded-list,
length, arbitrary-code reconstruction, or append-correctness supplier; any such
facts needed for the proof must be derived separately. No numeral-only prefix. -/
def InternalPreserveSome : Prop := ∀ n (p : Program n) appendTag lookupTag,
  (nodes p)[appendTag]? = some ⟨2,append⟩ → (nodes p)[lookupTag]? = some ⟨2,HistoryLookup.lookup⟩ →
  ∀ ctx (index left right entry : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (.imp (.equal (HistoryLookup.lookupCall lookupTag index left) (.succ entry))
      (.equal (HistoryLookup.lookupCall lookupTag index (appendCall appendTag left right)) (.succ entry))))

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryAppend.Targets
