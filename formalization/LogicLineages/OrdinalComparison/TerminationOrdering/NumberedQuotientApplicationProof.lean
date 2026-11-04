module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientApplicationTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientApplicationProof
open Source NumberedRewriteSyntax NumberedFiniteUniverse NumberedWindowEquivalence NumberedQuotientApplication

theorem applicationConfinement : NumberedQuotientApplicationTargets.ActualApplicationConfinement := by
  intro Symbol arity symbols S hc Gamma sigma tau f a hf ha
  have hft := NumberedUniverseOperationsProof.rootType (fun t => t ∈ S) (HeadInWindow arity symbols S) f hf
  have ht := NumberedUniverseOperationsProof.arrowCodomain (fun t => t ∈ S) hc sigma tau hft
  exact ⟨⟨ht,hf.1,ha.1⟩,hf.2,ha.2⟩

theorem representativeApplicationCongruence : NumberedQuotientApplicationTargets.ActualRepresentativeApplicationCongruence := by
  intro n arity symbols S hc Gamma sigma tau f g a b hf hg ha hb hfg hab
  have ef := (NumberedLeastCodeRepresentativeProof.representativeEquality n arity symbols S hc Gamma
    ⟨.arrow sigma tau,f⟩ ⟨.arrow sigma tau,g⟩ hf hg).mp hfg
  have ea := (NumberedLeastCodeRepresentativeProof.representativeEquality n arity symbols S hc Gamma
    ⟨sigma,a⟩ ⟨sigma,b⟩ ha hb).mp hab
  have e : WindowPrimary (Fin n) arity symbols S Gamma (applicationPacked f a) (applicationPacked g b) :=
    .trans (.appFunction f g a ef) (.appArgument g a b ea)
  exact (NumberedLeastCodeRepresentativeProof.representativeEquality n arity symbols S hc Gamma
    (applicationPacked f a) (applicationPacked g b)
    (applicationConfinement (Fin n) arity symbols S hc Gamma sigma tau f a hf ha)
    (applicationConfinement (Fin n) arity symbols S hc Gamma sigma tau g b hg hb)).mpr e

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientApplicationProof
