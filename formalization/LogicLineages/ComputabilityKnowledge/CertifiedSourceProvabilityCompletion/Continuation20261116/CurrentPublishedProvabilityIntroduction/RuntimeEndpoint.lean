module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.DoubleCore
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.InnerCode
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.OutputFormula
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.ClosedValidity
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.GraphProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.RuntimeEndpoint
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport

theorem current {n k ctx : Nat} (p : Program n) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (rawOld ar : Program 1) (x : Program 3)
 (I : CumulativePropositionalSource.JointInstallation p f lhs rhs t (CurrentQuantifierLogicalSource.selectedOld rawOld) ar x)
 (N : CurrentExistentialIntroductionProgram.LogicalInterface.Nodes p)
 (etag publishedTag : Nat)
 (he : (nodes p)[etag]? = some ⟨3,CurrentExistentialIntroductionProgram.program⟩)
 (hp : (nodes p)[publishedTag]? = some ⟨7,program⟩)
 (pF : Program 1) (c : Code) (sigma : Sentence) (G : List (Formula ctx))
 (innerFuel innerCert inputProof index outerFuel : Term ctx) :
 let old := CurrentQuantifierLogicalSource.selectedOld rawOld
 let R := RuntimeRebase.shared p f lhs rhs t old ar x I
 Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (core I.currentK.coreTag index outerFuel (checkerEquationCode (tags R.previous) pF c sigma innerFuel innerCert) inputProof) →
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (accepted I.currentK.coreTag I.currentK.verifierTag index outerFuel
   (Term.numeral (Encodable.encode (GorbowFormulaPrefixCode.encode (.imp (rho pF c) (prD pF c sigma)))))
   (outputCode publishedTag pF c sigma innerFuel innerCert inputProof))) := by
 let old := CurrentQuantifierLogicalSource.selectedOld rawOld
 let R := RuntimeRebase.shared p f lhs rhs t old ar x I
 let J := CurrentExistentialIntroductionProgram.RuntimeTags.tags R (N.singletonTag false) (N.singletonTag true)
 let K := tags R.previous
 let V := R.previous.previous.current
 let v : List.Vector (Term ctx) 7 := Term.numeral (GorbowNamedInternalProvability.checkerTag pF) ::ᵥ
  Term.numeral (Encodable.encode c) ::ᵥ innerFuel ::ᵥ innerCert ::ᵥ rawNumeral (PublishedSyntax.argument pF c sigma) ::ᵥ
  Term.numeral (Encodable.encode (GorbowFormulaPrefixCode.encode (rho pF c))) ::ᵥ inputProof ::ᵥ nil
 dsimp only
 intro hinput
 obtain ⟨hu⟩ := ValidityProof.closed p _ _ _ I.previous.current G (PublishedSyntax.argument pF c sigma)
 obtain ⟨hrho⟩ := ClosedValidity.formula p f lhs rhs t old ar x I G (rho pF c)
 have hraw := GuardSupport.inner p f lhs rhs t old ar x I K.numeralTag R.previous.previous.previous.previous.previous.hnumeral G v hu
 obtain ⟨hw⟩ := GuardSupport.numeralValid p f lhs rhs t old ar x I K.numeralTag R.previous.previous.previous.previous.previous.hnumeral G innerCert
 obtain ⟨hinstance⟩ := TemplateInstance.instantiated p _ _ _ V innerEnvironment bodyTemplate G
  (GraphInterface.innerInputs K.numeralTag v) (GraphInterface.numeral K.numeralTag innerCert) hraw hw
 obtain ⟨hcode⟩ := InnerCode.specialized p J K.numeralTag R.previous.current.h_ctag R.previous.current.h_atag R.previous.previous.previous.previous.previous.hnumeral v
 have heq := localTrans _ _ _ hinstance (.base hcode)
 have hrev := Hilbert.Local.mp (.base (Logic.symmetryRule (GorbowPRNumeralCalculation.Theory p) _ _)) heq
 obtain ⟨hin⟩ := PrescribedRuntimeEquality.LogicProof.coreFormula I.currentK.coreTag index outerFuel _ _ inputProof hrev hinput
 obtain ⟨hd⟩ := DoubleCore.current p f lhs rhs t rawOld ar x I N K.numeralTag etag R.previous.previous.previous.previous.previous.hnumeral he G v index outerFuel hu hrho hin
 have hdcore := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hd
 obtain ⟨houtformula⟩ := OutputFormula.published p J K R.previous.current.h_ctag R.previous.current.h_atag R.previous.previous.previous.previous.previous.hnumeral
  pF c sigma innerFuel innerCert inputProof
 obtain ⟨hformula⟩ := PrescribedRuntimeEquality.LogicProof.coreFormula I.currentK.coreTag index outerFuel _ _ _ (.base houtformula) hdcore
 have installed := CurrentExistentialIntroductionProgram.RuntimeTags.installed R (N.singletonTag false) (N.singletonTag true) (N.hsingle false) (N.hsingle true)
 obtain ⟨hgraph⟩ := GraphProof.graph p v J installed K.numeralTag etag R.previous.previous.previous.previous.previous.hnumeral he publishedTag hp
 obtain ⟨hfinal⟩ := CurrentImplicationCertificate.RebaseProof.coreCode (GorbowPRNumeralCalculation.Theory p) G
  I.currentK.coreTag index outerFuel _ _ _ (.base (Support.equalitySymmetry _ _ hgraph)) hformula
 exact CurrentImplicationCertificate.AlgebraSupport.acceptedOfCore p f lhs rhs t old ar x I _ (fun _ h => h) G _ _ index outerFuel hfinal
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.RuntimeEndpoint
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.RuntimeEndpoint
