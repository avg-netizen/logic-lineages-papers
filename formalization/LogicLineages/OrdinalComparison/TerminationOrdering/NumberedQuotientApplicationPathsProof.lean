module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientApplicationPathsTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientApplicationPathsProof
open Source NumberedRewriteSyntax NumberedFiniteUniverse NumberedLeastCodeRepresentative
open NumberedQuotientPaths NumberedQuotientApplication NumberedWindowTraces

theorem actualCountedFunctionApplication :
    NumberedQuotientApplicationPathsTargets.ActualCountedFunctionApplication := by
  intro n arity symbols S hc above Gamma sigma tau f g a hf hg ha count hp
  have htrace := NumberedQuotientPathsProof.countedBackward n arity symbols S hc above Gamma count
    ⟨.arrow sigma tau,f⟩ ⟨.arrow sigma tau,g⟩ hf hg hp
  have htyped := (NumberedWindowTracesProof.typedPresentation (Fin n) arity symbols S above Gamma
    (.arrow sigma tau) count f g).mp htrace
  have happ := NumberedWindowTracesProof.functionContext (Fin n) arity symbols S above Gamma
    sigma tau count f g a htyped
  have hpacked := (NumberedWindowTracesProof.typedPresentation (Fin n) arity symbols S above Gamma
    tau count (.app f a) (.app g a)).mpr happ
  exact NumberedQuotientPathsProof.countedForward n arity symbols S hc above Gamma count
    (applicationPacked f a) (applicationPacked g a)
    (NumberedQuotientApplicationProof.applicationConfinement (Fin n) arity symbols S hc Gamma sigma tau f a hf ha)
    hpacked

theorem actualPositiveFunctionApplication :
    NumberedQuotientApplicationPathsTargets.ActualPositiveFunctionApplication := by
  intro n arity symbols S hc above Gamma sigma tau f g a hf hg ha hp
  obtain ⟨count, hpos, hcount⟩ := (NumberedQuotientPathsProof.positiveClosure n arity symbols S above Gamma
    (representativeCode symbols S ⟨.arrow sigma tau,f⟩)
    (representativeCode symbols S ⟨.arrow sigma tau,g⟩)).mp hp
  apply (NumberedQuotientPathsProof.positiveClosure n arity symbols S above Gamma
    (representativeCode symbols S (applicationPacked f a))
    (representativeCode symbols S (applicationPacked g a))).mpr
  exact ⟨count, hpos, actualCountedFunctionApplication n arity symbols S hc above Gamma sigma tau
    f g a hf hg ha count hcount⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientApplicationPathsProof
