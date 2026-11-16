module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.NativeMatrices
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.PublishedSyntax
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.NativeSyntax
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.NativeProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
attribute [local irreducible] GorbowPRProgram.evaluate

theorem exactNative : Targets.Native := by
 intro pF c sigma fuel certificate inputProof
 let v := nativeInputs pF c sigma fuel certificate inputProof
 let u := PublishedSyntax.argument pF c sigma
 have hu : v.get 4 = Encodable.encode (GorbowTermPrefixCode.encode u) := rfl
 have hi := NativeMatrices.inner v u hu
 have ho := NativeMatrices.outer v u hu
 change evaluate innerMatrixProgram v = Encodable.encode (GorbowFormulaPrefixCode.encode
  (SyntaxSupport.checkerInner (GorbowNamedInternalProvability.checkerTag pF) (Encodable.encode c) fuel u)) at hi
 change evaluate outerMatrixProgram v = Encodable.encode (GorbowFormulaPrefixCode.encode
  (Formula.ex (SyntaxSupport.checkerBody (GorbowNamedInternalProvability.checkerTag pF) (Encodable.encode c) u))) at ho
 rw [← PublishedSyntax.inner pF c sigma fuel] at hi
 rw [← PublishedSyntax.outer pF c sigma] at ho
 have hcert := NativeInputs.quoted 3 v
 have hfuel := NativeInputs.quoted 2 v
 have hfirst := NativeMatrices.introduceEval innerMatrixProgram (quotedNumeral 3) (.projection 6) v
  (innerMatrix pF c sigma fuel) (Term.numeral certificate) hi hcert
 have hsecond := NativeMatrices.introduceEval outerMatrixProgram (quotedNumeral 2) innerProof v
  (outerMatrix pF c sigma) (Term.numeral fuel) ho hfuel
 have hex := CurrentExistentialIntroductionProgram.NativeSyntax.exEval outerMatrixProgram v (outerMatrix pF c sigma) ho
 rw [Preflight.literalOuter] at hex
 have hrho : evaluate (.projection (5 : Fin 7)) v = Encodable.encode (GorbowFormulaPrefixCode.encode (rho pF c)) := by
  unfold evaluate
  rfl
 have hinput : evaluate (.projection (6 : Fin 7)) v = inputProof := by
  unfold evaluate
  rfl
 have hfirst' : evaluate innerProof v = CurrentExistentialIntroductionProgram.number (innerMatrix pF c sigma fuel)
  (Term.numeral certificate) inputProof := by
  rw [hinput] at hfirst
  exact hfirst
 have hsecond' : evaluate outerProof v = CurrentExistentialIntroductionProgram.number (outerMatrix pF c sigma)
  (Term.numeral fuel) (CurrentExistentialIntroductionProgram.number (innerMatrix pF c sigma fuel)
   (Term.numeral certificate) inputProof) := by
  rw [hfirst'] at hsecond
  exact hsecond
 change evaluate (CurrentRecursionStepProgram.liftProgram _ _ _) v = _
 rw [CurrentRecursionStepProgram.NativeOperations.liftEval _ _ _ v (prD pF c sigma) (rho pF c) hex hrho,hsecond']
 rfl
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.NativeProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.NativeProof
