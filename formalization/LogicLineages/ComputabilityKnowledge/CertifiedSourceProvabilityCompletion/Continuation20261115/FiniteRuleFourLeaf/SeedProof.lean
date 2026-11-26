module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FiniteRuleFourLeaf.Targets
public import LogicLineages.ComputabilityKnowledge.GorbowTheoryCheckerProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FiniteRuleFourLeaf.SeedProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPublishedDCB GorbowTheoryProof SixSol20261113 List.Vector
/-- Original installed numeral graph; no native checker correctness is needed. -/
theorem graph {n : Nat} (p : Program n) (tag : Nat) (x : Program 3)
 (hx : (nodes p)[tag]? = some ⟨3,SaturatedAxiomLeaf.saturated x⟩)
 (c : Code) (fuel : Nat) (sigma : Sentence) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (graphEquation tag x c fuel sigma)) :=
 QuotedVerifierMP.QuotationProof.numeralCalculation p tag (SaturatedAxiomLeaf.saturated x) hx
  (arguments c fuel sigma) 0
/-- Exact original canonical rule4 payload, not an existential certificate. -/
theorem canonical (c : Code) (fuel : Nat) (sigma : Sentence)
 (h : GorbowEnumeratedProvability.boundedTheory (c,fuel) sigma) :
 GorbowTheoryChecker.axiomCheck (GorbowEnumeratedProvability.axiomCheck (c,fuel))
  (GorbowProofChecker.context (GorbowTheoryChecker.axiomLine 0 sigma))
  (GorbowProofChecker.conclusion (GorbowTheoryChecker.axiomLine 0 sigma))
  (GorbowProofChecker.payload (GorbowTheoryChecker.axiomLine 0 sigma)) = true := by
 apply (GorbowTheoryCheckerProof.axiomExact _ _ _ _).mpr
 exact ⟨sigma,rfl,h,rfl⟩
/-- Concrete original Line decoding and source-code index decoding only. -/
theorem evaluated (x : Program 3)
 (hx : ∀ v, evaluate x v = HistoryDispatcher.axiomFunction v)
 (c : Code) (fuel : Nat) (sigma : Sentence)
 (h : GorbowEnumeratedProvability.boundedTheory (c,fuel) sigma) :
 evaluate (SaturatedAxiomLeaf.saturated x) (arguments c fuel sigma) = 1 := by
 refine (SaturatedAxiomLeaf.StatementChecks.nativeCalibration x hx (arguments c fuel sigma)).trans ?_
 have hh := canonical c fuel sigma h
 simp only [HistoryDispatcher.axiomFunction,arguments,List.Vector.head_cons,List.Vector.tail_cons,
  lineCode,HistoryDispatcher.decodedLine,Encodable.encodek,Option.getD_some,Denumerable.ofNat_encode]
 rw [hh]
 rfl
/-- Rewrite the output of the actual defining-equation graph, at every context. -/
theorem seed {n : Nat} (p : Program n) (tag : Nat) (x : Program 3)
 (hx : (nodes p)[tag]? = some ⟨3,SaturatedAxiomLeaf.saturated x⟩)
 (hn : ∀ v, evaluate x v = HistoryDispatcher.axiomFunction v)
 (c : Code) (fuel : Nat) (sigma : Sentence)
 (h : GorbowEnumeratedProvability.boundedTheory (c,fuel) sigma) (ctx : Nat) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (SaturatedAxiomLeaf.success (ctx := ctx) tag (Term.numeral (Encodable.encode c))
   (Term.numeral fuel) (Term.numeral (lineCode sigma)))) := by
 obtain ⟨hg⟩ := QuotedVerifierMP.QuotationProof.numeralCalculation p tag
  (SaturatedAxiomLeaf.saturated x) hx (arguments c fuel sigma) ctx
 rw [evaluated x hn c fuel sigma h] at hg
 exact ⟨by simpa [SaturatedAxiomLeaf.success,SaturatedAxiomLeaf.leafCall,arguments,
  List.Vector.map_cons,List.Vector.map_nil,Term.numeral] using hg⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FiniteRuleFourLeaf.SeedProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FiniteRuleFourLeaf.SeedProof
