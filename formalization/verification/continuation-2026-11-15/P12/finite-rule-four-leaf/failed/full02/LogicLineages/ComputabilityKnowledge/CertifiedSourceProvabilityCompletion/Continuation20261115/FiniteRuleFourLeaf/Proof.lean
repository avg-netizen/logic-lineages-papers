module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FiniteRuleFourLeaf.SeedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FiniteRuleFourLeaf.Proof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPublishedDCB GorbowTheoryProof SixSol20261113
/-- Monotonicity is an internal theorem of the actual installed wrapper, not
an external larger-fuel success fact. -/
theorem largerSeed {n : Nat} (p : Program n) (tag : Nat) (x : Program 3)
 (hx : (nodes p)[tag]? = some ⟨3,SaturatedAxiomLeaf.saturated x⟩)
 (hn : ∀ v, evaluate x v = HistoryDispatcher.axiomFunction v)
 (c : Code) (fuel : Nat) (sigma : Sentence)
 (h : GorbowEnumeratedProvability.boundedTheory (c,fuel) sigma)
 (ctx : Nat) (larger : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (SixSol20261112.Fuel.orderGuard (Term.numeral fuel) larger)
   (SaturatedAxiomLeaf.success tag (Term.numeral (Encodable.encode c))
    larger (Term.numeral (lineCode sigma))))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := SixSol20261112.Fuel.orderGuard (Term.numeral fuel) larger
 obtain ⟨hs⟩ := SeedProof.seed p tag x hx hn c fuel sigma h ctx
 obtain ⟨hm⟩ := SaturatedAxiomLeaf.StatementChecks.internalMonotonicity n p tag x hx ctx
  (Term.numeral (Encodable.encode c)) (Term.numeral fuel) larger (Term.numeral (lineCode sigma))
 have hh : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
 have hout := Hilbert.Local.mp (Hilbert.Local.mp (Hilbert.Local.base hm) hh) (Hilbert.Local.base hs)
 exact ⟨hout.discharge.finish⟩
/-- The original source tuple and all root tags remain fixed throughout. -/
theorem finiteLiteralLeaf : Targets.FiniteLiteralLeaf := by
 intro pF pR q c hA x tag hn hx
 obtain ⟨fuel,hiff,hrest⟩ := FiniteSource.Proof.actualFixedFuelPackage pF pR q c hA
 refine ⟨fuel,?_⟩
 intro sigma hsigma
 have hS : S pF pR q sigma := List.mem_append_left _ (List.mem_append_left _ hsigma)
 have hb := (hiff sigma).mp hS
 refine ⟨SeedProof.graph (sourceRoot pF pR q) tag x hx c fuel sigma,
  SeedProof.seed (sourceRoot pF pR q) tag x hx hn c fuel sigma hb 0,?_⟩
 intro ctx larger
 have hd := largerSeed (sourceRoot pF pR q) tag x hx hn c fuel sigma hb ctx larger
 exact GorbowTheoryProofProof.monotonicity _ _
  (fun _ hs => List.mem_append_left _ (List.mem_append_left _ hs)) ctx _ hd
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FiniteRuleFourLeaf.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FiniteRuleFourLeaf.Proof
