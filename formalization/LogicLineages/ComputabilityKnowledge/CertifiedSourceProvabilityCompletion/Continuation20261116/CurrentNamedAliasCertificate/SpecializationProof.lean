module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedAliasCertificate.SeedProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.SeedRepeatedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedAliasCertificate.SpecializationProof
open GorbowSyntax GorbowPRProgram GorbowTheoryProof GorbowPublishedDCB SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open CumulativePropositionalSource

theorem specialized {k : Nat} (installed : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1) (c : Code)
 (hA : Actual pF pR (verifier installed lhs rhs old a baseX) c)
 (hn : ∀ v, evaluate baseX v = HistoryDispatcher.axiomFunction v)
 (I : JointInstallation (root installed lhs rhs pF pR old a baseX) installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX)) :
 ∃ seedFuel : Nat, ∀ ctx (G : List (Formula ctx)) (raw : List.Vector (Term ctx) 2) (larger : Term ctx),
 (∀ i, Nonempty (Hilbert.Local (S pF pR (verifier installed lhs rhs old a baseX)) ctx G
  (Continuation20261114.RawReflexivityDispatcher.valid I.previous.previous.current.vtag (raw.get i)))) →
 Nonempty (Hilbert.Local (S pF pR (verifier installed lhs rhs old a baseX)) ctx G
  (SixSol20261112.Fuel.orderGuard (Term.numeral seedFuel) larger)) →
 Nonempty (Hilbert.Local (S pF pR (verifier installed lhs rhs old a baseX)) ctx G
  (PrescribedRuntimeEquality.accepted I.currentK.coreTag I.currentK.verifierTag
   (Term.numeral (Encodable.encode c)) larger
   (PrescribedRuntimeSpecialization.value I.previous.previous.current.ctag I.previous.previous.current.atag matrix raw)
   (PrescribedSourceAxiomSpecialization.certificate I.previous.previous.previous.previous.previous.mpTag
    I.previous.previous.current.ctag I.previous.previous.current.atag I.previous.previous.current.constructorTag matrix raw))) := by
 let p := CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX
 let T := GorbowPRNumeralCalculation.Theory p
 let U := S pF pR (CumulativePropositionalSource.verifier installed lhs rhs old a baseX)
 let J := I.previous.previous.current
 let mtag := I.previous.previous.previous.previous.previous.mpTag
 let n := 2
 let f := matrix
 obtain ⟨seedFuel,hseed⟩ := SeedProof.seed installed lhs rhs t old a baseX pF pR c hA hn I
 refine ⟨seedFuel,?_⟩
 intro ctx G raw larger hinputs hguard
 obtain ⟨hc⟩ := hseed ctx larger
 obtain ⟨hg⟩ := hguard
 have hseedCore := Hilbert.Local.mp (Hilbert.Local.base (Gamma := G) hc) hg
 obtain ⟨hprior⟩ := PrescribedSourceAxiomSpecialization.SeedProof.doubleCode U G I.currentK.coreTag
  (Term.numeral (Encodable.encode c)) larger (Term.numeral (PrescribedSourceAxiomSpecialization.seed f))
  (GorbowStandardInduction.universalClosure f) hseedCore
 let C : Term ctx := Term.numeral (Encodable.encode (GorbowFormulaPrefixCode.encode
  (GorbowStandardInduction.universalClosure f)))
 let P := Formula.equal (LiteralCheckerAcceptance.coreCall I.currentK.coreTag
  (Term.numeral (Encodable.encode c)) larger .zero (.add C C)
  (Term.numeral (PrescribedSourceAxiomSpecialization.seed f))) (.succ .zero)
 let guards := List.ofFn (fun i : Fin n => Continuation20261114.RawReflexivityDispatcher.valid J.vtag (raw.get i))
 let Gamma := P :: guards
 have hi : ∀ i : Fin n, Nonempty (Hilbert.Local T ctx Gamma
  (Continuation20261114.RawReflexivityDispatcher.valid J.vtag (raw.get i))) := by
  intro i
  exact ⟨.hypothesis (List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨i,rfl⟩))⟩
 have hp : Nonempty (Hilbert.Local T ctx Gamma P) := ⟨.hypothesis List.mem_cons_self⟩
 have h := SeedRepeatedProof.repeated p installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX) I
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
  (SeedSourceProof.inclusion installed lhs rhs pF pR old a baseX) hG h
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedAliasCertificate.SpecializationProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedAliasCertificate.SpecializationProof
