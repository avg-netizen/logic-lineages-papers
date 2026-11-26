module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open GorbowRegistryTuple PrescribedRuntimeEquality PrescribedRuntimeCallCongruence HistoryRuleSuffix
/-- Raw term inputs are encodings; child certificates are unrestricted Nats. -/
def NativeTuple : Prop := ∀ n (xs ys : List.Vector (Term 0) n) (codes : List.Vector Nat n),
 evaluate (tupleProgram n) (pack (encodeTerms xs) (encodeTerms ys) codes) = tupleNumber xs ys codes
def NativeCall : Prop := ∀ n tag (xs ys : List.Vector (Term 0) n) (codes : List.Vector Nat n),
 evaluate (callProgram n) (tag ::ᵥ pack (encodeTerms xs) (encodeTerms ys) codes) = callNumber tag xs ys codes
/-- Arbitrary symbolic raw terms/codes, actual primitive and producer nodes only. -/
def InternalTuple : Prop := ∀ arity (p : Program arity) n (J : Tags) producerTag,
 Installation p J → (nodes p)[producerTag]? = some ⟨width n,tupleProgram n⟩ →
 ∀ ctx (xs ys codes : List.Vector (Term ctx) n),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (call producerTag (pack xs ys codes)) (tupleCertificate J xs ys codes)))
def InternalCall : Prop := ∀ arity (p : Program arity) n (J : Tags) producerTag,
 Installation p J → (nodes p)[producerTag]? = some ⟨width n+1,callProgram n⟩ →
 ∀ ctx (tag : Term ctx) (xs ys codes : List.Vector (Term ctx) n),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (call producerTag (tag ::ᵥ pack xs ys codes)) (callCertificate J tag xs ys codes)))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.Targets
