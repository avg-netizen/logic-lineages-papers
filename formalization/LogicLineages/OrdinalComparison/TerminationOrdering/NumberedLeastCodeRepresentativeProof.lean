module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedLeastCodeRepresentativeSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedLeastCodeRepresentativeProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedWindowEquivalence NumberedFinitePrimaryClass NumberedLeastCodeRepresentative

local instance {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty} : DecidableEq (Packed (Fin n) arity Gamma) := NumberedAuxiliaryCodingProof.packedDecidableEq

theorem structuralNumberInjective : NumberedLeastCodeRepresentativeTargets.ActualStructuralNumberInjective := NumberedLeastCodeRepresentativeSupportProof.structuralNumberInjective

theorem packedNumberInjective : NumberedLeastCodeRepresentativeTargets.ActualPackedNumberInjective := NumberedLeastCodeRepresentativeSupportProof.packedNumberInjective

theorem representativeAttained : NumberedLeastCodeRepresentativeTargets.ActualRepresentativeAttained := by
  intro n arity symbols S hc Gamma q hq
  have hm := Finset.min'_mem (classNumbers symbols S q) (classNumbersNonempty symbols S q)
  obtain ⟨r,hr,he⟩ := Finset.mem_image.mp hm
  exact ⟨r,(NumberedFinitePrimaryClassProof.exactPrimaryClass (Fin n) inferInstance arity symbols S hc Gamma q hq r).mp hr,he.symm⟩

theorem representativeMinimal : NumberedLeastCodeRepresentativeTargets.ActualRepresentativeMinimal := by
  intro n arity symbols S hc Gamma q r hq hqr
  have hr := (NumberedFinitePrimaryClassProof.exactPrimaryClass (Fin n) inferInstance arity symbols S hc Gamma q hq r).mpr hqr
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨r,hr,rfl⟩)

theorem equalClasses {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty}
    (symbols : List (Fin n)) (S : List Ty) (hc : SubtypeClosed (fun tau => tau∈S))
    (q r : Packed (Fin n) arity Gamma) (hq : InUniverse symbols S q.2) (hr : InUniverse symbols S r.2)
    (hqr : WindowPrimary (Fin n) arity symbols S Gamma q r) : primaryClass symbols S q=primaryClass symbols S r := by
  apply Finset.ext
  intro t
  rw [NumberedFinitePrimaryClassProof.exactPrimaryClass (Fin n) inferInstance arity symbols S hc Gamma q hq t,
      NumberedFinitePrimaryClassProof.exactPrimaryClass (Fin n) inferInstance arity symbols S hc Gamma r hr t]
  exact ⟨fun h => .trans (.symm hqr) h,fun h => .trans hqr h⟩

theorem representativeEquality : NumberedLeastCodeRepresentativeTargets.ActualRepresentativeEquality := by
  intro n arity symbols S hc Gamma q r hq hr
  constructor
  · intro he
    obtain ⟨a,ha,hca⟩ := representativeAttained n arity symbols S hc Gamma q hq
    obtain ⟨b,hb,hcb⟩ := representativeAttained n arity symbols S hc Gamma r hr
    have hab : a=b := packedNumberInjective n arity Gamma (hca.symm.trans (he.trans hcb))
    subst b
    exact .trans ha (.symm hb)
  · intro he
    have hclasses := equalClasses symbols S hc q r hq hr he
    have hcodes : classNumbers symbols S q=classNumbers symbols S r := congrArg (fun A => A.image packedNumber) hclasses
    unfold representativeCode
    simp only [hcodes]

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedLeastCodeRepresentativeProof
