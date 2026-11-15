module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRuntimeSpecializationStep.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRuntimeSpecializationStep.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
/-- Genuine one-step dynamic specialization preserving an arbitrary actually
accepted antecedent certificate. All programs and tags are chosen before the
formula/environment; no leaf acceptance, new-line validity, successful-run,
list-image or dynamic fixed-template assumption is added. Drop is recovered
from the actual installed lookup. Common index/fuel and numeric MP code remain exact. -/
def InternalSpecializationStep : Prop :=
 ∀ arity (p : Program arity) (old arithmetic : Program 1) (x : Program 3)
 (I : UniformClosedRule13Certificate.Installation p old arithmetic x) (mtag : Nat),
 (nodes p)[mtag]? = some ⟨4,LiteralRawMP.constructor⟩ →
 ∀ n inputs (e : FixedFormulaSubstitution.Environment n 1 inputs) (f : Formula n)
 ctx (G : List (Formula ctx)) (raw : List.Vector (Term ctx) inputs) (replacement antecedent index fuel : Term ctx),
 (∀ i : Fin inputs, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (Continuation20261114.RawReflexivityDispatcher.valid I.vtag (raw.get i)))) →
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (Continuation20261114.RawReflexivityDispatcher.valid I.vtag replacement)) →
 let U := FixedFormulaSubstitution.unaryValue I.ctag 10
  (FixedFormulaSubstitution.formulaValue I.ctag I.atag raw f e)
 let B := body I.ctag I.atag e f raw replacement
 let code := certificate mtag I.ctag I.atag I.constructorTag e f raw replacement antecedent
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (LiteralCheckerAcceptance.coreCall I.coreTag index fuel .zero (.add U U) antecedent) (.succ .zero))) →
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.conj
   (.equal (LiteralCheckerAcceptance.coreCall I.coreTag index fuel .zero (.add B B) code) (.succ .zero))
   (SixSol20261112.Fuel.success I.verifierTag index fuel .zero (.add B B) code)))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRuntimeSpecializationStep.Targets
