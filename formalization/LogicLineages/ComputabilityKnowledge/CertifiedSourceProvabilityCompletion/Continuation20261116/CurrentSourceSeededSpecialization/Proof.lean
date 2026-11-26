module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentSourceSeededSpecialization.RepeatedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentSourceSeededSpecialization.Proof
open GorbowSyntax GorbowPRProgram GorbowTheoryProof GorbowPublishedDCB SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
theorem seeded : Targets.InternalSeededSpecialization := by
 intro installed lhs rhs k t old a baseX pF pR c hA hn I
 let p := CumulativeUniformRule12Source.root installed lhs rhs pF pR old a baseX
 let T := GorbowPRNumeralCalculation.Theory p
 let U := S pF pR (CumulativeUniformRule12Source.verifier installed lhs rhs old a baseX)
 let J := I.previous.current
 let mtag := I.previous.previous.previous.previous.mpTag
 let IF := SourceProof.finiteInstallation p installed lhs rhs t old a baseX I
 obtain ⟨seedFuel,hseed⟩ := FiniteRuleFourCertificate.StatementChecks.exactFiniteLiteralCertificate
  (CumulativeUniformRule12Source.logical installed lhs rhs old)
  (CumulativeUniformRule12Source.arithmetic a) baseX pF pR c hA hn IF
 refine ⟨seedFuel,?_⟩
 intro n f hmem ctx G raw larger hinputs hguard
 obtain ⟨_,hc,_⟩ := hseed (GorbowStandardInduction.universalClosure f) hmem ctx larger
 obtain ⟨hc⟩ := hc
 obtain ⟨hg⟩ := hguard
 have hseedCore := Hilbert.Local.mp (Hilbert.Local.base (Gamma := G) hc) hg
 obtain ⟨hprior⟩ := PrescribedSourceAxiomSpecialization.SeedProof.doubleCode U G I.current.coreTag
  (Term.numeral (Encodable.encode c)) larger (Term.numeral (PrescribedSourceAxiomSpecialization.seed f))
  (GorbowStandardInduction.universalClosure f) hseedCore
 let C : Term ctx := Term.numeral (Encodable.encode (GorbowFormulaPrefixCode.encode
  (GorbowStandardInduction.universalClosure f)))
 let P := Formula.equal (LiteralCheckerAcceptance.coreCall I.current.coreTag
  (Term.numeral (Encodable.encode c)) larger .zero (.add C C)
  (Term.numeral (PrescribedSourceAxiomSpecialization.seed f))) (.succ .zero)
 let guards := List.ofFn (fun i : Fin n => Continuation20261114.RawReflexivityDispatcher.valid J.vtag (raw.get i))
 let Gamma := P :: guards
 have hi : ∀ i : Fin n, Nonempty (Hilbert.Local T ctx Gamma
  (Continuation20261114.RawReflexivityDispatcher.valid J.vtag (raw.get i))) := by
  intro i
  exact ⟨.hypothesis (List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨i,rfl⟩))⟩
 have hp : Nonempty (Hilbert.Local T ctx Gamma P) := ⟨.hypothesis List.mem_cons_self⟩
 have h := RepeatedProof.repeated p installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX) I
  n f ctx Gamma raw (Term.numeral (PrescribedSourceAxiomSpecialization.seed f))
  (Term.numeral (Encodable.encode c)) larger hi hp
 have hG : ∀ psi, psi ∈ Gamma → Nonempty (Hilbert.Local U ctx G psi) := by
  intro psi hmem
  rcases List.mem_cons.mp hmem with he | hg
  · subst psi
    exact ⟨hprior⟩
  · obtain ⟨i,he⟩ := List.mem_ofFn.mp hg
    subst psi
    exact hinputs i
 exact PrescribedSourceAxiomSpecialization.SourceSupportProof.localCut
  (SourceProof.inclusion installed lhs rhs pF pR old a baseX) hG h
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentSourceSeededSpecialization.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentSourceSeededSpecialization.Proof
