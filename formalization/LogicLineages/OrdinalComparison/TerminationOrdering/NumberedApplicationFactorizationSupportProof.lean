module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedApplicationFactorizationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryShapesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientApplicationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedApplicationFactorizationSupportProof
open Source NumberedRewriteSyntax NumberedFiniteUniverse NumberedWindowEquivalence
open NumberedAuxiliaryCoding NumberedLeastCodeRepresentative NumberedQuotientApplication

theorem pairMonoLeft (c : Nat) {a b : Nat} (h : a ≤ b) : Nat.pair a c ≤ Nat.pair b c := by
  rcases lt_or_eq_of_le h with h | h
  · exact (Nat.pair_lt_pair_left c h).le
  · subst b; exact Nat.le_refl _

theorem pairMonoRight (c : Nat) {a b : Nat} (h : a ≤ b) : Nat.pair c a ≤ Nat.pair c b := by
  rcases lt_or_eq_of_le h with h | h
  · exact (Nat.pair_lt_pair_right c h).le
  · subst b; exact Nat.le_refl _

theorem pairMono {a b c d : Nat} (h : a ≤ b) (k : c ≤ d) :
    Nat.pair a c ≤ Nat.pair b d :=
  (pairMonoLeft c h).trans (pairMonoRight b k)

theorem pairRightOrderReflection (c : Nat) {a b : Nat}
    (h : Nat.pair c a ≤ Nat.pair c b) : a ≤ b := by
  by_contra hn
  exact (Nat.not_lt_of_ge h) (Nat.pair_lt_pair_right c (Nat.lt_of_not_ge hn))

theorem packedPayloadOrder {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty} {tau : Ty}
    {f g : AuxTerm (Fin n) arity Gamma tau}
    (h : packedNumber ⟨tau,f⟩ ≤ packedNumber ⟨tau,g⟩) :
    codeNumber (termCode f) ≤ codeNumber (termCode g) :=
  pairRightOrderReflection (typeNumber tau) h

theorem applicationNumberMono {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty}
    {sigma tau : Ty} {f g : AuxTerm (Fin n) arity Gamma (.arrow sigma tau)}
    {a b : AuxTerm (Fin n) arity Gamma sigma}
    (hf : packedNumber ⟨.arrow sigma tau,f⟩ ≤ packedNumber ⟨.arrow sigma tau,g⟩)
    (ha : packedNumber ⟨sigma,a⟩ ≤ packedNumber ⟨sigma,b⟩) :
    packedNumber (applicationPacked f a) ≤ packedNumber (applicationPacked g b) := by
  exact pairMonoRight (typeNumber tau) (pairMonoRight 2
    (pairMonoRight (typeNumber sigma) (pairMono (packedPayloadOrder hf) (packedPayloadOrder ha))))

/-- The minimizer is recovered at the original type and in the original
window. No semantic/canonicality field is added to the term or class. -/
theorem typedRepresentative (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S : List Ty) (hc : SubtypeClosed (fun tau => tau ∈ S))
    (Gamma : List Ty) (tau : Ty) (f : AuxTerm (Fin n) arity Gamma tau)
    (hf : InUniverse symbols S f) :
    ∃ g : AuxTerm (Fin n) arity Gamma tau,
      InUniverse symbols S g ∧
      WindowPrimary (Fin n) arity symbols S Gamma ⟨tau,f⟩ ⟨tau,g⟩ ∧
      representativeCode symbols S ⟨tau,f⟩ = packedNumber ⟨tau,g⟩ ∧
      representativeCode symbols S ⟨tau,g⟩ = packedNumber ⟨tau,g⟩ := by
  obtain ⟨⟨rho,g⟩,hfg,he⟩ :=
    NumberedLeastCodeRepresentativeProof.representativeAttained n arity symbols S hc Gamma ⟨tau,f⟩ hf
  have ht := NumberedPrimaryEquivalenceProof.primaryTypePreservation (Fin n) arity Gamma _ _
    (NumberedWindowEquivalenceProof.actualPrimaryErasure (Fin n) arity symbols S Gamma _ _ hfg)
  change tau = rho at ht
  subst rho
  have hg : InUniverse symbols S g :=
    (NumberedWindowEquivalenceProof.actualPrimaryConfinement (Fin n) arity symbols S Gamma _ _ hfg).mp hf
  have hr := (NumberedLeastCodeRepresentativeProof.representativeEquality n arity symbols S hc Gamma
    ⟨tau,f⟩ ⟨tau,g⟩ hf hg).mpr hfg
  exact ⟨g,hg,hfg,he,hr.symm.trans he⟩

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedApplicationFactorizationSupportProof
end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedApplicationFactorizationSupportProof
