module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRuleSuffix.Definitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRuleSuffix.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector

/-- Calibration is to the original ruleCheck, not a new semantic checker. -/
def NativeMP : Prop := ∀ (h : GorbowProofChecker.History) (n : Nat) (raw : List Nat) r1 r2,
  evaluate mpCheck (Encodable.encode h ::ᵥ n ::ᵥ Encodable.encode raw ::ᵥ r1 ::ᵥ r2 ::ᵥ nil) =
    if GorbowProofChecker.ruleCheck h (GorbowProofChecker.mpLine n raw r1 r2) then 1 else 0

def NativeGeneralize : Prop := ∀ (h : GorbowProofChecker.History) (n : Nat) (raw : List Nat) r,
  evaluate generalizeCheck (Encodable.encode h ::ᵥ n ::ᵥ Encodable.encode raw ::ᵥ r ::ᵥ nil) =
    if GorbowProofChecker.ruleCheck h (GorbowProofChecker.generalizeLine n raw r) then 1 else 0

/-- Genuine internal rule2 suffix acceptance at arbitrary runtime terms.
No successful-reference or entry-reconstruction premise is assumed. -/
def InternalMPSuffix : Prop := ∀ arity (p : Program arity) tag appendTag,
  (nodes p)[tag]? = some ⟨5,mpCheck⟩ → (nodes p)[appendTag]? = some ⟨2,HistoryAppend.append⟩ →
  ∀ ctx (h tail n raw r1 r2 : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (.imp (.equal (mpCall tag h n raw r1 r2) (.succ .zero))
      (.equal (mpCall tag (HistoryAppend.appendCall appendTag h tail) n raw r1 r2) (.succ .zero))))

/-- Genuine internal rule3 suffix acceptance, with actual missing-reference guards.
Native calibration is not an internal premise. -/
def InternalGeneralizeSuffix : Prop := ∀ arity (p : Program arity) tag appendTag,
  (nodes p)[tag]? = some ⟨4,generalizeCheck⟩ → (nodes p)[appendTag]? = some ⟨2,HistoryAppend.append⟩ →
  ∀ ctx (h tail n raw r : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (.imp (.equal (generalizeCall tag h n raw r) (.succ .zero))
      (.equal (generalizeCall tag (HistoryAppend.appendCall appendTag h tail) n raw r) (.succ .zero))))

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRuleSuffix.Targets
