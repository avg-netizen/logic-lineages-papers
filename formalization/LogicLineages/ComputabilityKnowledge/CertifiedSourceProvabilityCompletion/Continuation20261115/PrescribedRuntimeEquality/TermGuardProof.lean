module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.TermGuardProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LiteralRawMP.DispatcherSupportProof TwoSol20261113.ReflexivityRecognizer
/-- Completeness of the actual installed closed-term predicate, paid by its
original equality-test binding rather than native validity reflection. -/
theorem complete {arity ctx : Nat} (p : Program arity) (old arithmetic : Program 1) (x : Program 3)
 (I : UniformClosedRule12Certificate.Installation p old arithmetic x)
 (G : List (Formula ctx)) (raw : Term ctx)
 (hs : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (LiteralSyntaxScan.scanCall I.stag (RawReflexivityDispatcher.TermSoundProof.tasks I.ptag I.ctag) raw) (.succ .zero))) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.vtag raw)) := by
 let g : Fin 2 → Program 1 := Fin.cases termScan (Fin.cases (HistoryRuleSuffix.constant 1 1) Fin.elim0)
 have he := SixSol20261112.Fuel.Equations.functionChild p I.vtag HistoryRuleSuffix.equalCode g I.h_vtag
 obtain ⟨hb⟩ := RawReflexivityDispatcher.TermSoundProof.binding p I.vtag I.stag I.ptag I.ctag (I.vtag+1)
  I.h_vtag I.h_stag I.h_ptag I.h_ctag he raw
 obtain ⟨hcomp⟩ := HistoryKernel.EqualProof.internalEqualComplete arity p (I.vtag+1) he ctx
  (LiteralSyntaxScan.scanCall I.stag (RawReflexivityDispatcher.TermSoundProof.tasks I.ptag I.ctag) raw) (.succ .zero)
 exact ⟨localTrans _ _ _ (.base hb) (Hilbert.Local.mp (.base hcomp) hs)⟩
theorem specialized {arity n inputs ctx : Nat} (p : Program arity) (old arithmetic : Program 1) (x : Program 3)
 (I : UniformClosedRule12Certificate.Installation p old arithmetic x)
 (e : FixedFormulaSubstitution.Environment n 1 inputs) (f : Term n)
 (G : List (Formula ctx)) (raw : List.Vector (Term ctx) inputs) (replacement : Term ctx)
 (hinputs : ∀ i : Fin inputs, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.vtag (raw.get i))))
 (hr : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (RawReflexivityDispatcher.valid I.vtag replacement)) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.vtag (specializedValue I.ctag I.atag e f raw replacement))) := by
 have hin : ∀ i : Fin (inputs+1), Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.vtag ((replacement ::ᵥ raw).get i))) := by
  intro i
  cases i using Fin.cases with
  | zero => exact ⟨hr⟩
  | succ j => exact hinputs j
 obtain ⟨hs⟩ := FullFormulaInstantiationValidity.FixedTermValidityProof.fixedTermValidity n 0 (inputs+1)
  (UniformRuntimeEnvironmentAgreement.specialize e) f arity p I.vtag I.stag I.ptag I.ctag I.atag
  I.h_vtag I.h_stag I.h_ptag I.h_ctag I.h_atag ctx G (replacement ::ᵥ raw) hin
 have hs' : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (LiteralSyntaxScan.scanCall I.stag (RawReflexivityDispatcher.TermSoundProof.tasks I.ptag I.ctag)
   (specializedValue I.ctag I.atag e f raw replacement)) (.succ .zero)) := by
  simpa only [specializedValue,FullFormulaInstantiationValidity.ClosedTermDepthTargets.tasks,
   RawReflexivityDispatcher.TermSoundProof.tasks,LiteralSyntaxStep.taskCall,LiteralNumeralPrefix.termTask,Term.numeral] using hs
 exact complete p old arithmetic x I G _ hs'
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.TermGuardProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.TermGuardProof
