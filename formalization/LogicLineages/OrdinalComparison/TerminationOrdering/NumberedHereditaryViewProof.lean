module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedHereditaryRootSignatureProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedHereditaryViewProof
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction
open NumberedFiniteUniverse NumberedWindowEquivalence NumberedLeastCodeRepresentative
open SourceZeroNumberedComputability
open NumberedHereditaryView NumberedPrimaryConstructorNormalizationProof
open NumberedPrimarySubstitution
open ID1Completion.SourceComputabilityCompletion

theorem memberUniverse {n : Nat} {arity : Fin n → Nat} {symbols : List (Fin n)} {S Gamma types : List Ty}
 (args : AuxArguments (Fin n) arity Gamma types) (h : GoodArgs symbols S args)
 (q : Packed (Fin n) arity Gamma) (hm : q ∈ argumentList args) : InUniverse symbols S q.2 := by
 induction types with
 | nil => cases args; cases hm
 | cons tau types ih => cases args with
   | cons a rest =>
     rcases List.mem_cons.mp hm with he | hm
     · cases he
       exact ⟨h.1.1,h.2.1⟩
     · exact ih rest ⟨h.1.2,h.2.2⟩ hm

theorem childUniverse {n : Nat} {arity : Fin n → Nat} {symbols : List (Fin n)} {S Gamma Delta : List Ty}
 {q : Packed (Fin n) arity Gamma} {a : Packed (Fin n) arity Delta}
 (h : Child q a) (hq : InUniverse symbols S q.2) : InUniverse symbols S a.2 := by
 cases h with
 | lam => exact ⟨hq.1.2.2,hq.2⟩
 | appFunction => exact ⟨hq.1.2.1,hq.2.1⟩
 | appArgument => exact ⟨hq.1.2.2,hq.2.2⟩
 | ordinary f base a hm => exact memberUniverse base ⟨hq.1.2,hq.2.2⟩ a hm
 | numberedBase k f tau base types extras a hm => exact memberUniverse base ⟨hq.1.2.1,hq.2.2.1⟩ a hm
 | numberedExtra k f tau base types extras a hm => exact memberUniverse extras ⟨hq.1.2.2,hq.2.2.2⟩ a hm

/-- BASE multiplicities are retained by the exact root permutation, so each
actual child has a matching actual child, not just a hypothesized partner. -/
theorem baseMatching {n : Nat} {arity : Fin n → Nat} {symbols : List (Fin n)} {S Gamma types otherTypes : List Ty}
 (a : AuxArguments (Fin n) arity Gamma types) (b : AuxArguments (Fin n) arity Gamma otherTypes)
 (hp : (argumentCodes symbols S a).Perm (argumentCodes symbols S b))
 (q : Packed (Fin n) arity Gamma) (hq : q ∈ argumentList a) :
 ∃ r : Packed (Fin n) arity Gamma, r ∈ argumentList b ∧ typedCode symbols S q = typedCode symbols S r := by
 have hm : typedCode symbols S q ∈ argumentCodes symbols S a := List.mem_map.mpr ⟨q,hq,rfl⟩
 have hn := hp.mem_iff.mp hm
 obtain ⟨r,hr,he⟩ := List.mem_map.mp hn
 exact ⟨r,hr,he.symm⟩

/-- Ordered extra codes give the original typed pointwise argument relation;
there is no BASE-style permutation of extras. -/
theorem extrasMatching {n : Nat} {arity : Fin n → Nat} {symbols : List (Fin n)} {S Gamma types : List Ty}
 (hc : SubtypeClosed (fun t => t ∈ S))
 (a b : AuxArguments (Fin n) arity Gamma types) (ha : GoodArgs symbols S a) (hb : GoodArgs symbols S b)
 (he : argumentCodes symbols S a = argumentCodes symbols S b) :
 WindowArgumentPrimary (Fin n) arity symbols S Gamma types a b := argumentsOfCodes hc a b ha hb he

theorem exactFiniteDepth : NumberedHereditaryViewTargets.ExactFiniteDepth := by
 intro n arity symbols S Gamma hc depth
 induction depth generalizing Gamma with
 | zero =>
   intro q r hq hr
   exact NumberedHereditaryRootSignatureProof.exactRootSignature n arity symbols S Gamma hc q r hq hr
 | succ depth ih =>
   intro q r hq hr
   constructor
   · intro h
     exact NumberedHereditaryRootSignatureProof.complete hc q r hq hr h.1
   · intro hp
     refine ⟨NumberedHereditaryRootSignatureProof.invariant hc hp hq,?_,?_⟩
     · intro Delta a b ha hb he
       have hau := childUniverse ha hq
       have hbu := childUniverse hb hr
       have hab := (NumberedLeastCodeRepresentativeProof.representativeEquality n arity symbols S hc Delta a b hau hbu).mp (congrArg Prod.snd he)
       exact (ih Delta a b hau hbu).mpr hab
     · intro binders tail sigma he
       cases he
       have hqe := OriginalClassContextPrefixNativeProof.prefixEraseUniverse n arity symbols S binders tail sigma q hq
       have hre := OriginalClassContextPrefixNativeProof.prefixEraseUniverse n arity symbols S binders tail sigma r hr
       have hpe := NumberedPrimarySubstitutionProof.actualPrimarySubstitution (Fin n) arity symbols S
         (binders ++ sigma :: tail) (binders ++ tail)
         (OriginalRawSyntaxTransport.prefixErasure binders tail sigma) q r hp
       exact (ih (binders ++ tail) _ _ hqe hre).mpr hpe

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedHereditaryViewProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedHereditaryViewProof
