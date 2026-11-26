module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedAxiomLeaf.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedAxiomLeaf.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof
open SixSol20261112
/-- Exact original axiom leaf semantics on ALL three-vectors, including
malformed/default encoded lines. This is a native calibration theorem only.
Its proof must establish external axiomFunction fuel monotonicity and use
bounded-search semantics, never reflect native facts into the source. -/
def NativeCalibration : Prop := ∀ x : Program 3,
 (∀ v, evaluate x v = HistoryDispatcher.axiomFunction v) →
 ∀ v, evaluate (saturated x) v = HistoryDispatcher.axiomFunction v
/-- Source-level monotonicity of the ACTUAL wrapper AST for arbitrary x.
No calibration, native Boolean range, universal evaluator or source-edge
premise is supplied. All runtime arguments and both bounds are internal. -/
def InternalMonotonicity : Prop := ∀ n (p : Program n) tag (x : Program 3),
 (nodes p)[tag]? = some ⟨3,saturated x⟩ →
 ∀ ctx (index s t line : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (Fuel.orderGuard s t) (.imp (success tag index s line) (success tag index t line))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedAxiomLeaf.Targets
