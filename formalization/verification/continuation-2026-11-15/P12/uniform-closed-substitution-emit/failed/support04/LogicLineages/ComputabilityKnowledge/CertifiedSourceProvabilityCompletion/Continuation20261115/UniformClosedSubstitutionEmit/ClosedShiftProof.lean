module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionEmit.Targets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FixedFormulaSubstitution.NativeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionEmit.ClosedShiftProof
open GorbowSyntax GorbowTermShiftCode
/-- Closed replacement terms have no free indices to shift. This derives the
raw-list identity from the original typed decoder and scanner invariant. -/
theorem closedShiftIdentity : Targets.ClosedShiftIdentity := by
 intro b raw hv
 obtain ⟨t,ht⟩ := (GorbowSyntaxValidationProof.exactTypedDomain.1 0 raw).mp hv
 have he := (GorbowTermPrefixCodeProof.decoderExact 0 raw t).mp ht
 subst raw
 have hs := congrArg Prod.snd (GorbowTermShiftCodeProof.scannerInvariant 0 b t [] [])
 have hraw : shiftRaw 0 b (GorbowTermPrefixCode.encode t) = GorbowTermPrefixCode.encode (shiftTerm b t) := by
  simpa only [shiftRaw,List.nil_append] using hs
 have hshift : shiftVar 0 b = (Fin.elim0 : Fin 0 → Fin (0+b)) := by
  funext i
  exact Fin.elim0 i
 rw [hraw,shiftTerm,hshift]
 exact FixedFormulaSubstitution.NativeProof.closedEncode (0+b) t
/-- Empty out-of-range dictionary replacement stays empty under the exact fold. -/
theorem emptyShift (b : Nat) : shiftRaw 0 b [] = [] := rfl
/-- Original lifted singleton dictionary, including out-of-range indices. -/
theorem liftedSingleton (b token : Nat) (raw : List Nat)
 (hv : GorbowSyntaxValidation.validTerm 0 raw = true) :
 GorbowLiftedDictionary.liftedCode 0 b [raw] token =
  if token < b then [0,token] else if token = b then raw else [] := by
 unfold GorbowLiftedDictionary.liftedCode
 split
 · rfl
 · rename_i hlt
   by_cases he : token = b
   · subst token
     simp only [Nat.sub_self,List.getD_cons_zero,closedShiftIdentity b raw hv,ite_true]
   · have hpos : 0 < token-b := by omega
     obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
     rw [hk]
     simp [List.getD,emptyShift,he]
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionEmit.ClosedShiftProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionEmit.ClosedShiftProof
