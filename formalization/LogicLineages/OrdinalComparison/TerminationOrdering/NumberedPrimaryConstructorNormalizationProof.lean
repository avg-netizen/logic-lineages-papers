module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryConstructorSignaturesTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryConstructorNormalizationProof
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction
open NumberedFiniteUniverse NumberedWindowEquivalence NumberedLeastCodeRepresentative
open SourceZeroNumberedComputability

/-- Proof-side choice only. Not a new executable selector or calibration. -/
theorem typedRepresentativeExists {n : Nat} {arity : Fin n → Nat} {symbols : List (Fin n)}
 {S Gamma : List Ty} (hc : SubtypeClosed (fun t => t ∈ S)) {tau : Ty}
 (q : AuxTerm (Fin n) arity Gamma tau) (hq : InUniverse symbols S q) :
 ∃ r : AuxTerm (Fin n) arity Gamma tau,
   WindowPrimary (Fin n) arity symbols S Gamma ⟨tau,q⟩ ⟨tau,r⟩ ∧
   packedNumber ⟨tau,r⟩ = representativeCode symbols S ⟨tau,q⟩ := by
 obtain ⟨⟨rho,r⟩,hp,he⟩ := NumberedLeastCodeRepresentativeProof.representativeAttained
   n arity symbols S hc Gamma ⟨tau,q⟩ hq
 have ht := NumberedPrimaryEquivalenceProof.primaryTypePreservation (Fin n) arity Gamma _ _
   (NumberedWindowEquivalenceProof.actualPrimaryErasure (Fin n) arity symbols S Gamma _ _ hp)
 change tau=rho at ht
 cases ht
 exact ⟨r,hp,he.symm⟩

noncomputable def normalTerm {n : Nat} {arity : Fin n → Nat} {symbols : List (Fin n)}
 {S Gamma : List Ty} (hc : SubtypeClosed (fun t => t ∈ S)) {tau : Ty}
 (q : AuxTerm (Fin n) arity Gamma tau) (hq : InUniverse symbols S q) : AuxTerm (Fin n) arity Gamma tau :=
 Classical.choose (typedRepresentativeExists hc q hq)

theorem normalTerm_spec {n : Nat} {arity : Fin n → Nat} {symbols : List (Fin n)}
 {S Gamma : List Ty} (hc : SubtypeClosed (fun t => t ∈ S)) {tau : Ty}
 (q : AuxTerm (Fin n) arity Gamma tau) (hq : InUniverse symbols S q) :
 WindowPrimary (Fin n) arity symbols S Gamma ⟨tau,q⟩ ⟨tau,normalTerm hc q hq⟩ ∧
 packedNumber ⟨tau,normalTerm hc q hq⟩ = representativeCode symbols S ⟨tau,q⟩ :=
 Classical.choose_spec (typedRepresentativeExists hc q hq)

abbrev GoodArgs {n : Nat} {arity : Fin n → Nat} (symbols : List (Fin n)) (S : List Ty)
 {Gamma types : List Ty} (args : AuxArguments (Fin n) arity Gamma types) :=
 NumberedUniverseBindingTargets.GoodArguments (fun t => t ∈ S) (HeadInWindow arity symbols S) args

noncomputable def normalArgs {n : Nat} {arity : Fin n → Nat} {symbols : List (Fin n)}
 {S Gamma : List Ty} (hc : SubtypeClosed (fun t => t ∈ S)) :
 {types : List Ty} → (args : AuxArguments (Fin n) arity Gamma types) → GoodArgs symbols S args →
 AuxArguments (Fin n) arity Gamma types
 | [], .nil, _ => .nil
 | _::_, .cons q rest, h => .cons (normalTerm hc q ⟨h.1.1,h.2.1⟩)
     (normalArgs hc rest ⟨h.1.2,h.2.2⟩)

theorem normalArgs_primary {n : Nat} {arity : Fin n → Nat} {symbols : List (Fin n)}
 {S Gamma : List Ty} (hc : SubtypeClosed (fun t => t ∈ S)) {types : List Ty}
 (args : AuxArguments (Fin n) arity Gamma types) (h : GoodArgs symbols S args) :
 WindowArgumentPrimary (Fin n) arity symbols S Gamma types args (normalArgs hc args h) := by
 induction types with
 | nil => cases args; exact .nil
 | cons tau types ih => cases args with
   | cons q rest =>
     exact .cons _ _ _ _ (normalTerm_spec hc q ⟨h.1.1,h.2.1⟩).1
       (ih rest ⟨h.1.2,h.2.2⟩)

theorem normalArgs_numbers {n : Nat} {arity : Fin n → Nat} {symbols : List (Fin n)}
 {S Gamma : List Ty} (hc : SubtypeClosed (fun t => t ∈ S)) {types : List Ty}
 (args : AuxArguments (Fin n) arity Gamma types) (h : GoodArgs symbols S args) :
 (argumentList (normalArgs hc args h)).map packedNumber = (argumentCodes symbols S args).map Prod.snd := by
 induction types with
 | nil => cases args; rfl
 | cons tau types ih => cases args with
   | cons q rest =>
     simpa only [normalArgs,argumentList,argumentCodes,List.map_cons] using
       congrArg₂ List.cons (normalTerm_spec hc q ⟨h.1.1,h.2.1⟩).2 (ih rest ⟨h.1.2,h.2.2⟩)

theorem normalArgs_perm {n : Nat} {arity : Fin n → Nat} {symbols : List (Fin n)}
 {S Gamma : List Ty} (hc : SubtypeClosed (fun t => t ∈ S)) {types otherTypes : List Ty}
 (a : AuxArguments (Fin n) arity Gamma types) (b : AuxArguments (Fin n) arity Gamma otherTypes)
 (ha : GoodArgs symbols S a) (hb : GoodArgs symbols S b)
 (hp : (argumentCodes symbols S a).Perm (argumentCodes symbols S b)) :
 (argumentList (normalArgs hc a ha)).Perm (argumentList (normalArgs hc b hb)) := by
 have h := hp.map Prod.snd
 rw [← normalArgs_numbers hc a ha,← normalArgs_numbers hc b hb] at h
 exact (List.map_perm_map_iff (NumberedLeastCodeRepresentativeProof.packedNumberInjective n arity Gamma)).mp h

theorem argumentCodes_types {n : Nat} {arity : Fin n → Nat} (symbols : List (Fin n)) (S : List Ty)
 {Gamma types : List Ty} (args : AuxArguments (Fin n) arity Gamma types) :
 (argumentCodes symbols S args).map Prod.fst = types := by
 induction types with
 | nil => cases args; rfl
 | cons tau types ih => cases args with
   | cons q rest => simpa only [argumentCodes,argumentList,List.map_cons,List.map_map,Function.comp_apply] using congrArg (List.cons tau) (ih rest)

theorem argumentsOfCodes {n : Nat} {arity : Fin n → Nat} {symbols : List (Fin n)}
 {S Gamma : List Ty} (hc : SubtypeClosed (fun t => t ∈ S)) {types : List Ty}
 (a b : AuxArguments (Fin n) arity Gamma types) (ha : GoodArgs symbols S a) (hb : GoodArgs symbols S b)
 (he : argumentCodes symbols S a = argumentCodes symbols S b) :
 WindowArgumentPrimary (Fin n) arity symbols S Gamma types a b := by
 induction types with
 | nil => cases a; cases b; exact .nil
 | cons tau types ih => cases a with
   | cons q rest => cases b with
     | cons r tail =>
       have hh := List.cons.inj he
       have hcode : representativeCode symbols S ⟨tau,q⟩ = representativeCode symbols S ⟨tau,r⟩ := congrArg Prod.snd hh.1
       have hp := (NumberedLeastCodeRepresentativeProof.representativeEquality n arity symbols S hc Gamma ⟨tau,q⟩ ⟨tau,r⟩ ⟨ha.1.1,ha.2.1⟩ ⟨hb.1.1,hb.2.1⟩).mp hcode
       exact .cons _ _ _ _ hp (ih rest tail ⟨ha.1.2,ha.2.2⟩ ⟨hb.1.2,hb.2.2⟩ hh.2)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryConstructorNormalizationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryConstructorNormalizationProof
