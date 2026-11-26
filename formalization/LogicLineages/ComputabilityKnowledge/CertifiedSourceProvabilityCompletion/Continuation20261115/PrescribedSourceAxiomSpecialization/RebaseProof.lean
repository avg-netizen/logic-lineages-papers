module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedSourceAxiomSpecialization.SourceSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedSourceAxiomSpecialization.RebaseProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB SixSol20261113
theorem repeated (old arithmetic : Program 1) (x : Program 3) (pF pR : Program 1)
 (I : UniformClosedRule13Certificate.Installation (root pF pR old arithmetic x)
  old arithmetic (SaturatedAxiomLeaf.saturated x)) (mtag : Nat)
 (hm : (nodes (root pF pR old arithmetic x))[mtag]? = some ⟨4,LiteralRawMP.constructor⟩)
 {n ctx : Nat} (f : Formula n) (G : List (Formula ctx)) (raw : List.Vector (Term ctx) n)
 (antecedent index fuel : Term ctx)
 (hinputs : ∀ i, Nonempty (Hilbert.Local (S pF pR (verifier old arithmetic x)) ctx G
  (Continuation20261114.RawReflexivityDispatcher.valid I.vtag (raw.get i))))
 (hprior : Nonempty (Hilbert.Local (S pF pR (verifier old arithmetic x)) ctx G
  (.equal (LiteralCheckerAcceptance.coreCall I.coreTag index fuel .zero
   (.add (Term.numeral (Encodable.encode (GorbowFormulaPrefixCode.encode (GorbowStandardInduction.universalClosure f))))
    (Term.numeral (Encodable.encode (GorbowFormulaPrefixCode.encode (GorbowStandardInduction.universalClosure f))))) antecedent) (.succ .zero)))) :
 Nonempty (Hilbert.Local (S pF pR (verifier old arithmetic x)) ctx G
  (.conj (.equal (LiteralCheckerAcceptance.coreCall I.coreTag index fuel .zero
   (.add (PrescribedRuntimeSpecialization.value I.ctag I.atag f raw)
    (PrescribedRuntimeSpecialization.value I.ctag I.atag f raw))
   (PrescribedRuntimeSpecialization.certificate mtag I.ctag I.atag I.constructorTag f raw antecedent)) (.succ .zero))
   (SixSol20261112.Fuel.success I.verifierTag index fuel .zero
    (.add (PrescribedRuntimeSpecialization.value I.ctag I.atag f raw)
     (PrescribedRuntimeSpecialization.value I.ctag I.atag f raw))
    (PrescribedRuntimeSpecialization.certificate mtag I.ctag I.atag I.constructorTag f raw antecedent)))) := by
 let T := GorbowPRNumeralCalculation.Theory (root pF pR old arithmetic x)
 let C : Term ctx := Term.numeral (Encodable.encode (GorbowFormulaPrefixCode.encode (GorbowStandardInduction.universalClosure f)))
 let P := Formula.equal (LiteralCheckerAcceptance.coreCall I.coreTag index fuel .zero (.add C C) antecedent) (.succ .zero)
 let guards := List.ofFn (fun i : Fin n => Continuation20261114.RawReflexivityDispatcher.valid I.vtag (raw.get i))
 let Gamma := P :: guards
 have hi : ∀ i : Fin n, Nonempty (Hilbert.Local T ctx Gamma
  (Continuation20261114.RawReflexivityDispatcher.valid I.vtag (raw.get i))) := by
  intro i
  exact ⟨.hypothesis (List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨i,rfl⟩))⟩
 have hp : Nonempty (Hilbert.Local T ctx Gamma P) := ⟨.hypothesis List.mem_cons_self⟩
 have h := PrescribedRuntimeSpecialization.StatementChecks.exactRepeatedSpecialization
  4 (root pF pR old arithmetic x) old arithmetic (SaturatedAxiomLeaf.saturated x) I mtag hm
  n f ctx Gamma raw antecedent index fuel hi hp
 have hG : ∀ psi, psi ∈ Gamma → Nonempty (Hilbert.Local (S pF pR (verifier old arithmetic x)) ctx G psi) := by
  intro psi hmem
  rcases List.mem_cons.mp hmem with he | hg
  · subst psi
    exact hprior
  · obtain ⟨i,he⟩ := List.mem_ofFn.mp hg
    subst psi
    exact hinputs i
 exact SourceSupportProof.localCut (SourceSupportProof.inclusion pF pR old arithmetic x) hG h
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedSourceAxiomSpecialization.RebaseProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedSourceAxiomSpecialization.RebaseProof
