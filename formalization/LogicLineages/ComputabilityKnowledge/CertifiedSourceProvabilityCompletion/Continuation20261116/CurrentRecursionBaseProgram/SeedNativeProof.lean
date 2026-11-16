module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseProgram.NativePrimitives
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseProgram.TagSyntax
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseProgram.SeedNativeProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open HistoryRuleSuffix.NativeProof GorbowFormulaSubstitution PrescribedRuntimeEquality
open NativePrimitives

theorem axiomEval {arity : Nat} (raw : Program arity) (v : List.Vector Nat arity) (f : Formula 0)
 (hf : evaluate raw v = Encodable.encode (GorbowFormulaPrefixCode.encode f)) :
 evaluate (axiomProgram raw) v = FiniteRuleFourCertificate.certificateCode f := by
 apply singletonEval
 simp only [twoEval,constantEval,hf,singleton,LiteralRawMP.NativeProof.pairEval,
  consEval]
 simp only [GorbowTheoryChecker.axiomLine,FiniteRuleFourCertificate.EncodingProof.closedIdentity,
  HistoryDispatcher.NativeProof.encodeProd,HistoryDispatcher.NativeProof.encodeNat,
  HistoryLookup.NativeProof.encodeCons]
 rfl

theorem seed {arity : Nat} (v : List.Vector Nat arity) (tag : Nat) (n : Nat)
 (f : Formula (n+1)) (raw : Fin (n+1) → Program arity) (sigma : Fin n → Term 0)
 (h : ∀ i, evaluate (raw i) v = Encodable.encode (GorbowTermPrefixCode.encode (TagSyntax.join tag sigma i))) :
 evaluate (seedProgram n f raw) v =
 PrescribedRuntimeSpecialization.produce (substituteFormula (TagSyntax.plug n tag) f) sigma
  (PrescribedSourceAxiomSpecialization.seed (substituteFormula (TagSyntax.plug n tag) f)) := by
 induction n with
 | zero =>
  have hs : TagSyntax.join tag sigma = TagSyntax.plug 0 tag := by
   funext i
   cases i using Fin.cases with
   | zero => rfl
   | succ i => exact Fin.elim0 i
  change evaluate (axiomProgram (quote f raw)) v = _
  have hq := quoteEval f raw v (TagSyntax.join tag sigma) h
  rw [hs] at hq
  exact axiomEval _ _ _ hq
 | succ n ih =>
  let sf := substituteFormula (TagSyntax.plug (n+1) tag) f
  let tailSigma : Fin n → Term 0 := fun i => sigma i.succ
  have ht : ∀ i, evaluate (raw i.succ) v = Encodable.encode (GorbowTermPrefixCode.encode (TagSyntax.join tag tailSigma i)) := by
   intro i
   simpa only [tailSigma,TagSyntax.tail] using h i.succ
  have hformula : evaluate (quote f raw) v = Encodable.encode (GorbowFormulaPrefixCode.encode (substituteFormula sigma sf)) := by
   rw [TagSyntax.formulaFull]
   exact quoteEval f raw v (TagSyntax.join tag sigma) h
  have hmatrix : evaluate (headQuote f (fun i => raw i.succ)) v =
   Encodable.encode (GorbowFormulaPrefixCode.encode (substituteFormula (liftSubstitute tailSigma) sf)) := by
   rw [TagSyntax.formulaHead]
   exact headQuoteEval f _ v (TagSyntax.join tag tailSigma) ht
  have hhead : evaluate (raw 0) v = Encodable.encode (GorbowTermPrefixCode.encode (sigma 0)) := by
   simpa only [TagSyntax.head] using h 0
  change evaluate (mp _ _ _) v = _
  rw [mpEval _ _ _ v _ hformula,allInstanceEval _ _ v _ _ hmatrix hhead]
  rw [ih (.all f) (fun i => raw i.succ) tailSigma ht]
  rfl
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseProgram.SeedNativeProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseProgram.SeedNativeProof
