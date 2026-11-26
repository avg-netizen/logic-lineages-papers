module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.ReflexivitySupport
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.ValiditySupport
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.FixedTemplateEncodingSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.TruthSupport
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality SixSol20261112.Fuel NamedArithmeticGraph
abbrev zeroCode {ctx : Nat} : Term ctx := Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode (Term.zero : Term 0)))
abbrev truthCode {ctx : Nat} : Term ctx := Term.numeral (Encodable.encode (GorbowFormulaPrefixCode.encode (.equal .zero .zero : Formula 0)))
variable {n k ctx : Nat} (p : Program n) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old ar : Program 1) (x : Program 3)
 (I : CumulativePropositionalSource.JointInstallation p f lhs rhs t old ar x)
 (G : List (Formula ctx))
theorem zeroValid : Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
 (RawReflexivityDispatcher.valid I.previous.current.vtag zeroCode)) := by
 let J := I.previous.current
 let e : FixedFormulaSubstitution.Environment 0 0 0 := Fin.elim0
 obtain ⟨hs⟩ := FullFormulaInstantiationValidity.FixedTermValidityProof.fixedTermValidity 0 0 0 e (.zero : Term 0)
  n p J.vtag J.stag J.ptag J.ctag J.atag J.h_vtag J.h_stag J.h_ptag J.h_ctag J.h_atag ctx G nil (fun i => Fin.elim0 i)
 apply TermGuardProof.complete p _ _ _ J G zeroCode
 simpa only [FixedFormulaSubstitution.termValue,FullFormulaInstantiationValidity.ClosedTermDepthTargets.tasks,
  RawReflexivityDispatcher.TermSoundProof.tasks,LiteralSyntaxStep.taskCall,LiteralNumeralPrefix.termTask,Term.numeral,
  zeroCode,GorbowTermPrefixCode.encode] using hs

theorem equation : Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.equal (equalValue I.previous.current.ctag I.previous.current.atag (zeroCode : Term ctx) zeroCode) truthCode)) :=
 FullFormulaInstantiationValidity.FixedTemplateEncodingSupportProof.binary p I.previous.current.ctag I.previous.current.atag
  I.previous.current.h_ctag I.previous.current.h_atag 0 zeroCode zeroCode
  (GorbowTermPrefixCode.encode (Term.zero : Term 0)) (GorbowTermPrefixCode.encode (Term.zero : Term 0))
  (.logical (.reflexive _)) (.logical (.reflexive _))

theorem certificate (index fuel : Term ctx) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (core I.currentK.coreTag index fuel truthCode
   (RawCumulativeLogical.certificate I.previous.current.ctag I.previous.previous.previous.previous.previous.reflexivityTag zeroCode))) := by
 obtain ⟨hv⟩ := zeroValid p f lhs rhs t old ar x I G
 obtain ⟨hc⟩ := ReflexivitySupport.current p f lhs rhs t old ar x I G zeroCode index fuel hv
 obtain ⟨he⟩ := equation (ctx := ctx) p f lhs rhs t old ar x I
 exact LogicProof.coreFormula I.currentK.coreTag index fuel _ _ _ (.base he) hc
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.TruthSupport
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.TruthSupport
