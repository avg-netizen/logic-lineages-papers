module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryConstructorNormalizationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryConstructorSignaturesProof
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction
open NumberedFiniteUniverse NumberedWindowEquivalence NumberedLeastCodeRepresentative
open SourceZeroNumberedComputability

open NumberedPrimaryConstructorNormalizationProof
open SourceConstructorPrimaryMeasuresSupportProof

def constructorClass {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
 (q : Packed Symbol arity Gamma) : Option (RecursiveComparison.HeadClass Symbol) :=
 match q with
 | ⟨_,.ordinary f _⟩ => some (RecursiveComparison.headClass f)
 | ⟨_,.numbered _ f _ _ _ _⟩ => some (RecursiveComparison.headClass f)
 | _ => none

theorem primaryConstructorClass {Symbol : Type} {arity : Symbol → Nat} {symbols : List Symbol}
 {S Gamma : List Ty} {q r : Packed Symbol arity Gamma}
 (h : WindowPrimary Symbol arity symbols S Gamma q r) : constructorClass q = constructorClass r := by
 induction h using WindowPrimary.rec (motive_2 := fun _ _ _ _ _ => True)
 case refl => rfl
 case symm h ih => exact ih.symm
 case trans h k ih ik => exact ih.trans ik
 case ordinary f g base target hf hg he ht hp => exact congrArg some he
 case numbered k f g tau base target types extras hf hg he hp => exact congrArg some he
 all_goals first | rfl | trivial

theorem ordinaryIff : NumberedPrimaryConstructorSignaturesTargets.OrdinaryIff := by
 intro n arity symbols S Gamma hc f g base target hq hr
 constructor
 · intro h
   exact ⟨Option.some.inj (primaryConstructorClass h),
     NumberedPrimaryEquivalenceProof.primaryTypePreservation (Fin n) arity Gamma _ _
       (NumberedWindowEquivalenceProof.actualPrimaryErasure (Fin n) arity symbols S Gamma _ _ h),
     primaryConstructorBaseCodes hc h hq⟩
 · rintro ⟨hhead,ht,hperm⟩
   have ha : GoodArgs symbols S base := ⟨hq.1.2,hq.2.2⟩
   have hb : GoodArgs symbols S target := ⟨hr.1.2,hr.2.2⟩
   have pa := normalArgs_primary hc base ha
   have pb := normalArgs_primary hc target hb
   have perm := normalArgs_perm hc base target ha hb hperm
   exact .trans (.ordinaryArguments f base (normalArgs hc base ha) pa)
     (.trans (.ordinary f g (normalArgs hc base ha) (normalArgs hc target hb)
       hq.2.1 hr.2.1 hhead ht perm)
       (.symm (.ordinaryArguments g target (normalArgs hc target hb) pb)))

theorem numberedIff : NumberedPrimaryConstructorSignaturesTargets.NumberedIff := by
 intro n arity symbols S Gamma hc k l f g tau upsilon base target types otherTypes extras otherExtras hq hr
 constructor
 · intro h
   exact ⟨Option.some.inj (SourceZeroNumberedShapeProof.primaryLabel h),
     NumberedPrimaryEquivalenceProof.primaryTypePreservation (Fin n) arity Gamma _ _
       (NumberedWindowEquivalenceProof.actualPrimaryErasure (Fin n) arity symbols S Gamma _ _ h),
     Option.some.inj (primaryConstructorClass h),primaryConstructorBaseCodes hc h hq,
     primaryConstructorExtraCodes hc h hq⟩
 · rintro ⟨rfl,rfl,hhead,hbase,hextra⟩
   have htypes : types = otherTypes := by
     rw [← argumentCodes_types symbols S extras,← argumentCodes_types symbols S otherExtras,hextra]
   subst otherTypes
   have ha : GoodArgs symbols S base := ⟨hq.1.2.1,hq.2.2.1⟩
   have hb : GoodArgs symbols S target := ⟨hr.1.2.1,hr.2.2.1⟩
   have pa := normalArgs_primary hc base ha
   have pb := normalArgs_primary hc target hb
   have perm := normalArgs_perm hc base target ha hb hbase
   have pe := argumentsOfCodes hc extras otherExtras ⟨hq.1.2.2,hq.2.2.2⟩ ⟨hr.1.2.2,hr.2.2.2⟩ hextra
   exact .trans (.numberedBase _ f _ base (normalArgs hc base ha) types extras pa)
     (.trans (.numbered _ f g _ (normalArgs hc base ha) (normalArgs hc target hb)
       types extras hq.2.1 hr.2.1 hhead perm)
       (.trans (.symm (.numberedBase _ g _ target (normalArgs hc target hb) types extras pb))
         (.numberedExtras _ g _ target types extras otherExtras pe)))

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryConstructorSignaturesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryConstructorSignaturesProof
