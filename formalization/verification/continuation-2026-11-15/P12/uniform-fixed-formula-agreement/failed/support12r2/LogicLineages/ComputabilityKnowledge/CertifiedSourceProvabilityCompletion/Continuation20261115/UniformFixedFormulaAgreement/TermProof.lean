module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.VariableProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.UnaryProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.BinaryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.TermProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph Traversal
open RelationalSyntaxDepthTransport.ConstructorStepTargets
/-- All original six term constructors; the sole free variable remains runtime
data and the pending stack/output are arbitrary symbolic codes. -/
theorem traverses {n ctx : Nat} (p : Program n) (I : Installation p)
 (depth : Nat) (t : Term (depth+1)) (raw : Term ctx) :
 ∀ rest out : Term ctx, Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (run I (GorbowTermPrefixCode.encode t)
   (.succ (HistoryLookup.consCall I.ctag (LiteralSyntaxStep.taskCall I.ptag 0 (Term.numeral (depth+1))) rest)) out raw)
   (HistoryKernel.pairCall I.ptag (.succ rest)
    (HistoryAppend.appendCall I.atag out
     (FixedFormulaSubstitution.termValue I.ctag I.atag (EnvironmentProof.environment depth) (raw ::ᵥ nil) t))))) := by
 induction t with
 | var i =>
  intro rest out
  exact VariableProof.traverses p I depth i rest out raw
 | zero =>
  intro rest out
  obtain ⟨hz⟩ := OneTokenProof.constructor p I (.term 1) (by intro h; cases h)
   (Term.numeral (depth+1)) rest out raw
  obtain ⟨hcode⟩ := PrefixCodeProof.encoded p I.ctag I.hc [1] (ctx := ctx)
  have hout := OutputProof.rightCongruence I.atag out _ _ hcode
  have hp := HistoryIteratorSuffix.ReconstructionProof.pairCongruence
   (T := GorbowPRNumeralCalculation.Theory p) (G := []) I.ptag (.succ rest) _ (.succ rest) _
   (.base (.logical (.reflexive _))) (.base hout)
  exact ⟨Logic.trans _ _ _ hz hp.finish⟩
 | succ t ih =>
  intro rest out
  exact UnaryProof.traverses p I (.term 2) (by intro h; cases h)
   (Term.numeral (depth+1)) (Term.numeral (depth+1)) 0 (GorbowTermPrefixCode.encode t)
   (FixedFormulaSubstitution.termValue I.ctag I.atag (EnvironmentProof.environment depth) (raw ::ᵥ nil) t)
   raw rfl ih rest out
 | add t u ht hu =>
  intro rest out
  exact BinaryProof.traverses p I (.term 3) (by intro h; cases h) (Term.numeral (depth+1)) 0
   (GorbowTermPrefixCode.encode t) (GorbowTermPrefixCode.encode u)
   (FixedFormulaSubstitution.termValue I.ctag I.atag (EnvironmentProof.environment depth) (raw ::ᵥ nil) t)
   (FixedFormulaSubstitution.termValue I.ctag I.atag (EnvironmentProof.environment depth) (raw ::ᵥ nil) u)
   raw rfl ht hu rest out
 | mul t u ht hu =>
  intro rest out
  exact BinaryProof.traverses p I (.term 4) (by intro h; cases h) (Term.numeral (depth+1)) 0
   (GorbowTermPrefixCode.encode t) (GorbowTermPrefixCode.encode u)
   (FixedFormulaSubstitution.termValue I.ctag I.atag (EnvironmentProof.environment depth) (raw ::ᵥ nil) t)
   (FixedFormulaSubstitution.termValue I.ctag I.atag (EnvironmentProof.environment depth) (raw ::ᵥ nil) u)
   raw rfl ht hu rest out
 | universalFunction t ih =>
  intro rest out
  exact UnaryProof.traverses p I (.term 5) (by intro h; cases h)
   (Term.numeral (depth+1)) (Term.numeral (depth+1)) 0 (GorbowTermPrefixCode.encode t)
   (FixedFormulaSubstitution.termValue I.ctag I.atag (EnvironmentProof.environment depth) (raw ::ᵥ nil) t)
   raw rfl ih rest out
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.TermProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.TermProof
