module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCheckerSuccessBridge.ValidityProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCheckerSuccessBridge.EncodingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCheckerSuccessBridge.ExternalProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
open SixSol20261112.Fuel NamedArithmeticGraph
/-- Intermediate form only: the original external guard APIs are used honestly.
The frozen endpoint's internal guard is discharged separately by its witness. -/
def External : Prop :=
 ∀ (f : Formula 1) (lhs rhs : Term 1) (old a : Program 1) (baseX : Program 3)
 (pF0 pR : Program 1) (pCK : Program 2) (box : Program 6) (c : Code),
 let t := CurrentNamedHeaderCertificate.template
 let pF := GorbowNamedInternalProvability.augment (GorbowNamedInternalProvability.augment pF0 pCK) box
 let q := CumulativePropositionalSource.verifier f lhs rhs old a baseX
 let root := CumulativePropositionalSource.root f lhs rhs pF pR old a baseX
 Actual pF pR q c →
 (∀ v, evaluate baseX v = HistoryDispatcher.axiomFunction v) →
 ∀ I : CumulativePropositionalSource.JointInstallation root f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX),
 ∀ (carrierTag peelTag baseProducerTag checkerInventoryTag checkerProducerTag : Nat),
 (nodes root)[carrierTag]? = some ⟨6,CurrentStructuralProducerInventory.carrier f lhs rhs t old a baseX pF0⟩ →
 (nodes root)[peelTag]? = some ⟨3,RuntimeOffsetAugmentationProducer.program⟩ →
 (nodes root)[baseProducerTag]? = some ⟨2,CurrentStructuralProducerCompiler.compile pF0⟩ →
 (nodes root)[checkerInventoryTag]? = some ⟨6,CurrentStructuralProducerInventory.carrier f lhs rhs t old a baseX q⟩ →
 (nodes root)[checkerProducerTag]? = some ⟨6,CurrentStructuralProducerCompiler.compile q⟩ →
 let R := CurrentPublishedProvabilityIntroduction.RuntimeRebase.shared root f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX) I
 ∃ bound : Nat, ∀ (sigma : Sentence) ctx (innerFuel innerCert outerFuel : Term ctx),
 let K := tags R.previous
 let r : Term ctx := Term.numeral (GorbowSortedSyntaxCode.formulaCode (rho pF c))
 let s : Term ctx := Term.numeral (GorbowSortedSyntaxCode.formulaCode sigma)
 let literalProof := RetainedBaseLiteralBinary.certificate K R.previous.previous.current.constructorTag
  R.previous.previous.previous.previous.template.certificateTag pF0 pCK box q peelTag baseProducerTag r s
 let checkerProof := CurrentCheckerSuccessCertificate.proofCode checkerProducerTag pF c innerFuel (value pF c sigma) innerCert
 Nonempty (Derivation (S pF pR q) (SixSol20261112.Fuel.orderGuard (Term.numeral bound) outerFuel)) →
 Nonempty (Derivation (S pF pR q)
   (.imp (CurrentCheckerSuccessCertificate.success pF c innerFuel (value pF c sigma) innerCert)
    (accepted R.currentK.coreTag R.currentK.verifierTag (Term.numeral (Encodable.encode c)) outerFuel
     (CurrentPublishedProvabilityIntroduction.checkerEquationCode K pF c sigma innerFuel innerCert)
     (certificate K pF c sigma innerFuel innerCert literalProof checkerProof))))

theorem external : External := by
 intro f lhs rhs old a baseX pF0 pR pCK box c
 dsimp only
 intro hA hbase I carrierTag peelTag baseProducerTag checkerInventoryTag checkerProducerTag hcarrier hpeel hbaseProducer hcheckerInventory hcheckerProducer
 let t := CurrentNamedHeaderCertificate.template
 let pF := GorbowNamedInternalProvability.augment (GorbowNamedInternalProvability.augment pF0 pCK) box
 let q := CumulativePropositionalSource.verifier f lhs rhs old a baseX
 let root := CumulativePropositionalSource.root f lhs rhs pF pR old a baseX
 let R := CurrentPublishedProvabilityIntroduction.RuntimeRebase.shared root f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX) I
 let K := tags R.previous
 let U := S pF pR q
 let incl := CumulativePropositionalSource.SeedSourceProof.inclusion f lhs rhs pF pR old a baseX
 obtain ⟨lb,hliteral⟩ := InstalledLiteralBinaryProducer.BoxLiteral.exactLiteral f lhs rhs old a baseX pF0 pR pCK box c
  hA hbase I carrierTag peelTag baseProducerTag hcarrier hpeel hbaseProducer
 obtain ⟨cb,hcompiler⟩ := CurrentStructuralProducerCore.StatementChecks.exactSource f lhs rhs 2 t old a baseX pF pR c hA hbase R
 refine ⟨lb+cb,?_⟩
 intro sigma ctx innerFuel innerCert outerFuel
 dsimp only
 intro hg
 obtain ⟨hg⟩ := hg
 obtain ⟨hlg⟩ := CurrentRecursionProducerCore.GuardBound.lowerAdd U lb cb outerFuel
 obtain ⟨hcg⟩ := CurrentRecursionProducerCore.GuardBound.lowerAdd U cb lb outerFuel
 rw [Nat.add_comm cb lb] at hcg
 let r : Term ctx := Term.numeral (GorbowSortedSyntaxCode.formulaCode (rho pF c))
 let s : Term ctx := Term.numeral (GorbowSortedSyntaxCode.formulaCode sigma)
 let literalProof := RetainedBaseLiteralBinary.certificate K R.previous.previous.current.constructorTag
  R.previous.previous.previous.previous.template.certificateTag pF0 pCK box q peelTag baseProducerTag r s
 let checkerProof := CurrentCheckerSuccessCertificate.proofCode checkerProducerTag pF c innerFuel (value pF c sigma) innerCert
 let index : Term ctx := Term.numeral (Encodable.encode c)
 let xs := leftArgs K pF c sigma innerFuel innerCert
 let PA := core R.currentK.coreTag index outerFuel (equalValue K.ctag K.atag (xs.get 3)
  ((rightArgs K pF c sigma innerFuel innerCert).get 3)) literalProof
 let PC := core R.currentK.coreTag index outerFuel
  (CurrentCheckerSuccessCertificate.quotedSuccess K pF c innerFuel (value pF c sigma) innerCert) checkerProof
 let success := CurrentCheckerSuccessCertificate.success pF c innerFuel (value pF c sigma) innerCert
 obtain ⟨hl⟩ := hliteral ctx r s outerFuel ⟨.mp hlg hg⟩
 have hlCore := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) (Hilbert.Local.base (Gamma := [success]) hl)
 let H := CurrentRecursionProducerCore.FormulaBridge.originalNodes root f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX) R
 obtain ⟨he⟩ := EncodingProof.rawBinary (ctx := ctx) root K H
  (GorbowSortedSyntaxCode.formulaCode (rho pF c)) (GorbowSortedSyntaxCode.formulaCode sigma)
 obtain ⟨hef⟩ := CurrentCompositionCertificate.CodecProof.binary root K.ctag K.atag K.ctag K.atag 0
  H.hc H.ha H.hc H.ha _ _ _ _ he (.logical (.reflexive (LiteralNumeralPrefix.numeralCall K.numeralTag (value pF c sigma))))
 obtain ⟨hefU⟩ := GorbowTheoryProofProof.monotonicity _ U incl ctx _ ⟨hef⟩
 obtain ⟨hlCore'⟩ := PrescribedRuntimeSpecialization.BaseProof.coreTransport U [success] R.currentK.coreTag index outerFuel _ _ literalProof (.base hefU) hlCore
 have hAcore : Hilbert.Local U ctx [success] PA := hlCore'
 have hchecker := GorbowNamedInternalProvability.Proof.exactCheckerTag 5 pF pR q
 obtain ⟨hc⟩ := hcompiler 5 q checkerInventoryTag hcheckerInventory 5 q (.here q rfl)
  (GorbowNamedInternalProvability.checkerTag pF) checkerProducerTag hchecker hcheckerProducer ctx
  (CurrentCheckerSuccessCertificate.checkerInputs c innerFuel (value pF c sigma) innerCert) outerFuel ⟨.mp hcg hg⟩
 have hcCore := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) (Hilbert.Local.base (Gamma := [success]) hc)
 obtain ⟨heq⟩ := CurrentCheckerSuccessCertificate.LocalQuotation.resultOne U K pF c innerFuel (value pF c sigma) innerCert
 obtain ⟨hcCore'⟩ := PrescribedRuntimeSpecialization.BaseProof.coreTransport U [success] R.currentK.coreTag index outerFuel _ _ checkerProof heq hcCore
 have hCcore : Hilbert.Local U ctx [success] PC := hcCore'
 let Gamma := [PA,PC]
 obtain ⟨ha⟩ := AlgebraProof.derive root f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX) R Gamma pF c sigma
  innerFuel innerCert literalProof checkerProof index outerFuel
  (ValidityProof.left root f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX) R Gamma pF c sigma innerFuel innerCert)
  (ValidityProof.right root f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX) R Gamma pF c sigma innerFuel innerCert)
  (.hypothesis (by change PA ∈ [PA,PC]; exact List.mem_cons_self))
  (.hypothesis (by change PC ∈ [PA,PC]; exact List.mem_cons_of_mem PA List.mem_cons_self))
 have hcut : ∀ psi, psi ∈ Gamma → Nonempty (Hilbert.Local U ctx [success] psi) := by
  intro psi hm
  simp only [Gamma,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with h | h
  · subst psi; exact ⟨hAcore⟩
  · subst psi; exact ⟨hCcore⟩
 obtain ⟨hout⟩ := PrescribedSourceAxiomSpecialization.SourceSupportProof.localCut incl hcut ⟨ha⟩
 exact ⟨hout.discharge.finish⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCheckerSuccessBridge.ExternalProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCheckerSuccessBridge.ExternalProof
