module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedApplicationFactorizationSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedApplicationFactorizationProof
open Source NumberedRewriteSyntax NumberedFiniteUniverse NumberedWindowEquivalence
open NumberedAuxiliaryCoding NumberedLeastCodeRepresentative NumberedQuotientApplication
open NumberedApplicationFactorizationSupportProof

theorem actualCanonicalChildrenApplicationFixed :
    NumberedApplicationFactorizationTargets.ActualCanonicalChildrenApplicationFixed := by
  intro n arity symbols S hc Gamma sigma tau f a hf ha hfc hac
  have happ := NumberedQuotientApplicationProof.applicationConfinement
    (Fin n) arity symbols S hc Gamma sigma tau f a hf ha
  apply Nat.le_antisymm
  · exact NumberedLeastCodeRepresentativeProof.representativeMinimal n arity symbols S hc Gamma
      (applicationPacked f a) (applicationPacked f a) happ (.refl _)
  · obtain ⟨r,hr,he⟩ := NumberedLeastCodeRepresentativeProof.representativeAttained
      n arity symbols S hc Gamma (applicationPacked f a) happ
    obtain ⟨g,b,rfl,hfg,hab⟩ :=
      (NumberedPrimaryShapesProof.actualPrimaryApplicationComponents
        (Fin n) arity symbols S Gamma sigma tau f a r).mp hr
    have hfl := NumberedLeastCodeRepresentativeProof.representativeMinimal n arity symbols S hc Gamma
      ⟨.arrow sigma tau,f⟩ ⟨.arrow sigma tau,g⟩ hf hfg
    have hal := NumberedLeastCodeRepresentativeProof.representativeMinimal n arity symbols S hc Gamma
      ⟨sigma,a⟩ ⟨sigma,b⟩ ha hab
    rw [hfc] at hfl
    rw [hac] at hal
    rw [he]
    exact applicationNumberMono hfl hal

theorem actualRepresentativeApplicationFactorization :
    NumberedApplicationFactorizationTargets.ActualRepresentativeApplicationFactorization := by
  intro n arity symbols S hc Gamma sigma tau f a hf ha
  obtain ⟨g,hg,hfg,heg,hgc⟩ := typedRepresentative n arity symbols S hc Gamma (.arrow sigma tau) f hf
  obtain ⟨b,hb,hab,heb,hbc⟩ := typedRepresentative n arity symbols S hc Gamma sigma a ha
  have hrep := NumberedQuotientApplicationProof.representativeApplicationCongruence
    n arity symbols S hc Gamma sigma tau f g a b hf hg ha hb
    (heg.trans hgc.symm) (heb.trans hbc.symm)
  have hfixed := actualCanonicalChildrenApplicationFixed
    n arity symbols S hc Gamma sigma tau g b hg hb hgc hbc
  rw [hrep,hfixed,heg,heb]
  simp only [packedNumber,applicationPacked,termCode,codeNumber,Nat.unpair_pair]

theorem actualCanonicalApplicationChildrenFixed :
    NumberedApplicationFactorizationTargets.ActualCanonicalApplicationChildrenFixed := by
  intro n arity symbols S hc Gamma sigma tau f a hf ha happ
  obtain ⟨g,hg,hfg,heg,hgc⟩ := typedRepresentative n arity symbols S hc Gamma (.arrow sigma tau) f hf
  obtain ⟨b,hb,hab,heb,hbc⟩ := typedRepresentative n arity symbols S hc Gamma sigma a ha
  have hrep := NumberedQuotientApplicationProof.representativeApplicationCongruence
    n arity symbols S hc Gamma sigma tau f g a b hf hg ha hb
    (heg.trans hgc.symm) (heb.trans hbc.symm)
  have hfixed := actualCanonicalChildrenApplicationFixed
    n arity symbols S hc Gamma sigma tau g b hg hb hgc hbc
  have he : packedNumber (applicationPacked f a) = packedNumber (applicationPacked g b) :=
    happ.symm.trans (hrep.trans hfixed)
  change Nat.pair (typeNumber tau)
      (Nat.pair 2 (Nat.pair (typeNumber sigma)
        (Nat.pair (codeNumber (termCode f)) (codeNumber (termCode a))))) =
    Nat.pair (typeNumber tau)
      (Nat.pair 2 (Nat.pair (typeNumber sigma)
        (Nat.pair (codeNumber (termCode g)) (codeNumber (termCode b))))) at he
  have hp := (Nat.pair_eq_pair.mp (Nat.pair_eq_pair.mp (Nat.pair_eq_pair.mp he).2).2).2
  obtain ⟨hfun,harg⟩ := Nat.pair_eq_pair.mp hp
  constructor
  · rw [heg]
    exact congrArg (Nat.pair (typeNumber (.arrow sigma tau))) hfun.symm
  · rw [heb]
    exact congrArg (Nat.pair (typeNumber sigma)) harg.symm

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedApplicationFactorizationProof
end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedApplicationFactorizationProof
