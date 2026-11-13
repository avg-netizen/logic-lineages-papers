module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.FuelWitness.InjectionPointwiseProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.FuelWitness.InjectionProof
open GorbowSyntax GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261112.Fuel NamedArithmeticGraph InjectionPointwiseProof

theorem internalInjection : Targets.InternalInjection := by
 intro n p vtag qtag q0 hv hq ctx index fuel context formula cert
 let T := GorbowPRNumeralCalculation.Theory p
 let W := Formula.conj (orderGuard (.var 0) (liftTerm fuel))
  (success qtag (liftTerm index) (.var 0) (liftTerm context) (liftTerm formula) (liftTerm cert))
 let R := success vtag index fuel context formula cert
 obtain ⟨hi⟩ := coreIntoVerifier p vtag qtag q0 hv hq
  (liftTerm index) (.var 0) (liftTerm context) (liftTerm formula) (liftTerm cert)
 obtain ⟨hm⟩ := InductionProof.openMonotonicity n p vtag q0 hv (ctx+1)
  (liftTerm index) (.var 0) (liftTerm fuel) (liftTerm context) (liftTerm formula) (liftTerm cert)
 have hw : Hilbert.Local T (ctx+1) [W] W := .hypothesis List.mem_cons_self
 have hbound := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hw
 have hcore := Hilbert.Local.mp (.base (.logical (.andRight _ _))) hw
 have hres := Hilbert.Local.mp (.mp (.base hm) hbound) (.mp (.base hi) hcore)
 have hbody : Derivation T (.imp W (GorbowPACore.weaken R)) := by
  simpa only [R,GorbowPACore.weaken,substSuccess,liftTerm,renameTerm] using
   Hilbert.Local.finish (Hilbert.Local.discharge hres)
 exact HBQuantifier.existentialElimination T W R ⟨hbody⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.FuelWitness.InjectionProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.FuelWitness.InjectionProof
