module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedVerifierCore.Targets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedCoreFuel.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.FuelWitness.StatementChecks
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedVerifierCore.Proof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261112.Fuel NamedArithmeticGraph LiteralCheckerAuxiliaries

theorem internalEquivalence : Targets.InternalEquivalence := by
 intro v l a x n p vtag qtag hv hq ctx index fuel context formula cert
 let T := GorbowPRNumeralCalculation.Theory p
 let q0 := LiteralKernelSource.coreChecker v l a (SaturatedAxiomLeaf.saturated x) bound initial finalizer
 let W := Formula.conj (orderGuard (.var 0) (liftTerm fuel))
  (success qtag (liftTerm index) (.var 0) (liftTerm context) (liftTerm formula) (liftTerm cert))
 let R := success qtag index fuel context formula cert
 obtain ⟨hm⟩ := SaturatedCoreFuel.StatementChecks.internalMonotonicity v l a x n p qtag hq (ctx+1)
  (liftTerm index) (.var 0) (liftTerm fuel) (liftTerm context) (liftTerm formula) (liftTerm cert)
 have hw : Hilbert.Local T (ctx+1) [W] W := .hypothesis List.mem_cons_self
 have hbound := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hw
 have hcore := Hilbert.Local.mp (.base (.logical (.andRight _ _))) hw
 have hresult := Hilbert.Local.mp (.mp (.base hm) hbound) hcore
 have hbody : Derivation T (.imp W (GorbowPACore.weaken R)) := by
  simpa only [R,GorbowPACore.weaken,FuelWitness.InjectionPointwiseProof.substSuccess,
   liftTerm,renameTerm,SaturatedCoreFuel.acceptance,success,LiteralCheckerAcceptance.coreCall,
   inputs,Term.numeral,substituteFormula,Logic.substCall,substitute,
   List.Vector.map_cons,List.Vector.map_nil] using Hilbert.Local.finish (Hilbert.Local.discharge hresult)
 obtain ⟨hbounded⟩ := HBQuantifier.existentialElimination T W R ⟨hbody⟩
 obtain ⟨hextract⟩ := FuelWitness.StatementChecks.exactExtraction n p vtag qtag q0 hv hq ctx index fuel context formula cert
 obtain ⟨hreverse⟩ := FuelWitness.InjectionPointwiseProof.coreIntoVerifier p vtag qtag q0 hv hq index fuel context formula cert
 have hforward := Hilbert.compose hbounded hextract
 exact ⟨.mp (.mp (.logical (.andIntro _ _)) hforward) hreverse⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedVerifierCore.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedVerifierCore.Proof
