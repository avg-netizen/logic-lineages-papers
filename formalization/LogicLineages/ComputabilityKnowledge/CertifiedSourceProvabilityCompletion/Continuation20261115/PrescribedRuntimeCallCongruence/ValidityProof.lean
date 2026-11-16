module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.ValidityProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
theorem term {arity n inputs ctx : Nat} (p : Program arity) (old arithmetic : Program 1) (x : Program 3)
 (I : UniformClosedRule12Certificate.Installation p old arithmetic x)
 (e : FixedFormulaSubstitution.Environment n 0 inputs) (f : Term n)
 (G : List (Formula ctx)) (raw : List.Vector (Term ctx) inputs)
 (hinputs : ∀ i : Fin inputs, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.vtag (raw.get i)))) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.vtag (FixedFormulaSubstitution.termValue I.ctag I.atag e raw f))) := by
 obtain ⟨hs⟩ := FullFormulaInstantiationValidity.FixedTermValidityProof.fixedTermValidity n 0 inputs e f arity p
  I.vtag I.stag I.ptag I.ctag I.atag I.h_vtag I.h_stag I.h_ptag I.h_ctag I.h_atag ctx G raw hinputs
 have hs' : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (LiteralSyntaxScan.scanCall I.stag (RawReflexivityDispatcher.TermSoundProof.tasks I.ptag I.ctag)
   (FixedFormulaSubstitution.termValue I.ctag I.atag e raw f)) (.succ .zero)) := by
  simpa only [FullFormulaInstantiationValidity.ClosedTermDepthTargets.tasks,
   RawReflexivityDispatcher.TermSoundProof.tasks,LiteralSyntaxStep.taskCall,LiteralNumeralPrefix.termTask,Term.numeral] using hs
 exact PrescribedRuntimeEquality.TermGuardProof.complete p old arithmetic x I G _ hs'
theorem closed {arity ctx : Nat} (p : Program arity) (old arithmetic : Program 1) (x : Program 3)
 (I : UniformClosedRule12Certificate.Installation p old arithmetic x)
 (G : List (Formula ctx)) (t : Term 0) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.vtag (PrescribedRuntimeEquality.rawNumeral t))) := by
 let e := FullFormulaInstantiationValidity.FixedTemplateEncodingTargets.boundEnvironment 0
 obtain ⟨hv⟩ := term p old arithmetic x I e t G nil (fun i => Fin.elim0 i)
 obtain ⟨he⟩ := FullFormulaInstantiationValidity.FixedTemplateEncodingProof.boundTermEncoding 0 t arity p
  I.ctag I.atag I.h_ctag I.h_atag ctx
 have heq := HistoryLookup.DestructorProof.unaryCallCongruence I.vtag _ _ he
 exact ⟨HistoryCodec.ArithmeticSupport.localTrans _ _ _
  (.base (Support.equalitySymmetry _ _ heq)) hv⟩
theorem numeral {arity ctx : Nat} (p : Program arity) (old arithmetic : Program 1) (x : Program 3)
 (I : UniformClosedRule12Certificate.Installation p old arithmetic x) (ntag : Nat)
 (hn : (nodes p)[ntag]? = some ⟨1,LiteralNumeralPrefix.numeralCode⟩)
 (G : List (Formula ctx)) (count : Term ctx) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.vtag (LiteralNumeralPrefix.numeralCall ntag count))) := by
 obtain ⟨hscan⟩ := LiteralNumeralPrefix.StatementChecks.exactScan arity p ntag I.stag I.ptag I.ctag
  hn I.h_stag I.h_ptag I.h_ctag ctx count .zero .zero
 exact RawSuccCongruence.ValidityProof.localBinding p G I.vtag I.stag I.ptag I.ctag
  I.h_vtag I.h_stag I.h_ptag I.h_ctag (LiteralNumeralPrefix.numeralCall ntag count) (.base hscan)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.ValidityProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.ValidityProof
