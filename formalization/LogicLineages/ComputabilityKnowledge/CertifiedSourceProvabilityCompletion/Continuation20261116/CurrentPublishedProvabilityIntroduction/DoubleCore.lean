module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.GuardSupport
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.TemplateInstance
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.BodyCongruence
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.TransformerCore
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.DoubleCore
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open PrescribedRuntimeEquality GraphInterface

theorem current {n k ctx : Nat} (p : Program n) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (rawOld ar : Program 1) (x : Program 3)
 (I : CumulativePropositionalSource.JointInstallation p f lhs rhs t (CurrentQuantifierLogicalSource.selectedOld rawOld) ar x)
 (N : CurrentExistentialIntroductionProgram.LogicalInterface.Nodes p)
 (ntag etag : Nat) (hn : (nodes p)[ntag]? = some ⟨1,LiteralNumeralPrefix.numeralCode⟩)
 (he : (nodes p)[etag]? = some ⟨3,CurrentExistentialIntroductionProgram.program⟩)
 (G : List (Formula ctx)) (v : List.Vector (Term ctx) 7) (index fuel : Term ctx)
 (hu : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (RawReflexivityDispatcher.valid I.previous.current.vtag (v.get 4)))
 (hrho : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (UniformClosedPropositional.formulaValid I.currentK.fval (v.get 5))) :
 let old := CurrentQuantifierLogicalSource.selectedOld rawOld
 let R := RuntimeRebase.shared p f lhs rhs t old ar x I
 let J := CurrentExistentialIntroductionProgram.RuntimeTags.tags R (N.singletonTag false) (N.singletonTag true)
 let V := R.previous.previous.current.toDispatcherInstallation.toInstallation
 Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (core I.currentK.coreTag index fuel (CurrentNegatedInstanceBridge.instanceValue V
   (innerValue J ntag v) (numeral ntag (v.get 3))) (v.get 6)) →
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (accepted I.currentK.coreTag I.currentK.verifierTag index fuel
   (impValue J.ctag J.atag (v.get 5) (FixedFormulaSubstitution.unaryValue J.ctag 11 (outerValue J ntag v)))
   (value J ntag etag v))) := by
 let old := CurrentQuantifierLogicalSource.selectedOld rawOld
 let R := RuntimeRebase.shared p f lhs rhs t old ar x I
 let J := CurrentExistentialIntroductionProgram.RuntimeTags.tags R (N.singletonTag false) (N.singletonTag true)
 let V := R.previous.previous.current
 dsimp only
 intro hinput
 have hir := GuardSupport.inner p f lhs rhs t old ar x I ntag hn G v hu
 have hor := GuardSupport.outer p f lhs rhs t old ar x I ntag hn G v hu
 obtain ⟨hcvalid⟩ := GuardSupport.numeralValid p f lhs rhs t old ar x I ntag hn G (v.get 3)
 obtain ⟨hfvalid⟩ := GuardSupport.numeralValid p f lhs rhs t old ar x I ntag hn G (v.get 2)
 obtain ⟨hinner⟩ := UniformRuntimeEnvironmentCertificate.GuardProof.validFormula p _ _ _ V innerEnvironment bodyTemplate G (innerInputs ntag v) hir
 obtain ⟨houter⟩ := UniformRuntimeEnvironmentCertificate.GuardProof.validFormula p _ _ _ V outerEnvironment (.ex bodyTemplate) G (outerInputs ntag v) hor
 have hg1 := Hilbert.Local.mp (.mp (.base (.logical (.andIntro _ _))) hinner) hcvalid
 obtain ⟨hfirst⟩ := CurrentExistentialIntroductionProgram.TransformerCore.current p f lhs rhs t rawOld ar x R N etag he
  G (innerValue J ntag v) (numeral ntag (v.get 3)) (v.get 6) index fuel hg1 hinput
 have hfirstCore := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hfirst
 obtain ⟨hinst⟩ := TemplateInstance.instantiated p _ _ _ V outerEnvironment (.ex bodyTemplate) G
  (outerInputs ntag v) (numeral ntag (v.get 2)) hor hfvalid
 obtain ⟨hspec⟩ := BodyCongruence.outerSpecialization p J R.previous.current.h_ctag R.previous.current.h_atag ntag v
 have hid := localTrans _ _ _ hinst (.base hspec)
 have hrev := Hilbert.Local.mp (.base (Logic.symmetryRule (GorbowPRNumeralCalculation.Theory p) _ _)) hid
 obtain ⟨hsecondInput⟩ := PrescribedRuntimeEquality.LogicProof.coreFormula I.currentK.coreTag index fuel _ _ _ hrev hfirstCore
 have hg2 := Hilbert.Local.mp (.mp (.base (.logical (.andIntro _ _))) houter) hfvalid
 obtain ⟨hsecond⟩ := CurrentExistentialIntroductionProgram.TransformerCore.current p f lhs rhs t rawOld ar x R N etag he
  G (outerValue J ntag v) (numeral ntag (v.get 2)) _ index fuel hg2 hsecondInput
 have hsecondCore := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hsecond
 obtain ⟨hex⟩ := CurrentExistentialIntroductionProgram.ValiditySupport.existential p f lhs rhs t old ar x R G (outerValue J ntag v) houter
 obtain ⟨hlift⟩ := CurrentExistentialIntroductionProgram.RuntimeAlgebra.lift p f lhs rhs t old ar x R
  (N.singletonTag false) (N.singletonTag true) G (FixedFormulaSubstitution.unaryValue J.ctag 11 (outerValue J ntag v))
  (v.get 5) _ index fuel hex hrho hsecondCore
 exact CurrentImplicationCertificate.AlgebraSupport.acceptedOfCore p f lhs rhs t old ar x R _ (fun _ h => h) G _ _ index fuel hlift
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.DoubleCore
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.DoubleCore
