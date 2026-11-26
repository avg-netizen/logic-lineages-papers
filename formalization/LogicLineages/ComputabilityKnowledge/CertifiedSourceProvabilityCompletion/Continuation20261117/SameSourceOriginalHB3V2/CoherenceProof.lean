module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceOriginalHB3V2.ComparatorGate
public import LogicLineages.ComputabilityKnowledge.GorbowPRInternalCoherenceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceOriginalHB3V2.CoherenceProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116
open SixSol20261112.Fuel NamedArithmeticGraph
open GorbowSubstitution GorbowFormulaSubstitution
/-- Two real occurrences of the SAME verifier AST, never equality of tags. -/
theorem calls (f : Formula 1) (lhs rhs : Term 1) (old a pF pR : Program 1) (baseX : Program 3)
 (tag : Nat)
 (h : (nodes (CumulativePropositionalSource.root f lhs rhs pF pR old a baseX))[tag]? =
  some ⟨5,CumulativePropositionalSource.verifier f lhs rhs old a baseX⟩)
 {ctx : Nat} (args : List.Vector (Term ctx) 5) :
 Nonempty (Derivation (S pF pR (CumulativePropositionalSource.verifier f lhs rhs old a baseX))
  (.equal (call tag args) (call (GorbowNamedInternalProvability.checkerTag pF) args))) := by
 have hn := GorbowNamedInternalProvability.Proof.exactCheckerTag 5 pF pR
  (CumulativePropositionalSource.verifier f lhs rhs old a baseX)
 obtain ⟨he⟩ := GorbowPRInternalCoherence.Proof.registryCoherence _
  (CumulativePropositionalSource.root f lhs rhs pF pR old a baseX) tag
  (GorbowNamedInternalProvability.checkerTag pF) 5 _ h hn ctx args
 exact GorbowTheoryProofProof.monotonicity _ _
  (CumulativePropositionalSource.SeedSourceProof.inclusion f lhs rhs pF pR old a baseX) ctx _ ⟨he⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceOriginalHB3V2.CoherenceProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceOriginalHB3V2.CoherenceProof
