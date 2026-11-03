module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedConfinedSourceSimulationTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedConfinedSourceSimulationProof
open Source Source.SourceMarkedSyntax Source.SourceTypeSupport LiteralContexts
open NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse
open NumberedWindowCertificates NumberedWindowTraces NumberedOrdinaryWindow
open NumberedLeastCodeRepresentative NumberedQuotientPaths

private theorem sourceMembership {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty}
    {tau : Ty} (s : Term (Fin n) arity Gamma tau) (u : Ty) :
    u ∈ NumberedConfinedSourceSimulation.sourceWindow s ↔ u ∈ typeSupport s := by
  simp only [NumberedConfinedSourceSimulation.sourceWindow,
    ← SourcePortContextsProof.literalTypeEnumeration (Fin n) arity Gamma tau s,
    List.mem_toFinset]

theorem sourceWindow : NumberedConfinedSourceSimulationTargets.ActualSourceWindow := by
  intro n arity above Gamma tau s t h
  have hc : SubtypeClosed (fun u => u ∈ NumberedConfinedSourceSimulation.sourceWindow s) := by
    intro u hu v hv
    exact (sourceMembership s v).mpr
      (SourceTypeSupportProof.subtypeClosedSupport (Fin n) arity Gamma tau s u
        ((sourceMembership s u).mp hu) v hv)
  have hs : typesAllowed (fun u => u ∈ NumberedConfinedSourceSimulation.sourceWindow s)
      (embed s) := by
    apply (TypeClosureProof.literalEmbeddingTypeClosure (Fin n) arity _ Gamma tau s hc).mpr
    intro u hu
    exact (sourceMembership s u).mpr hu
  have ht : typesAllowed (fun u => u ∈ NumberedConfinedSourceSimulation.sourceWindow s)
      (embed t) := by
    apply (TypeClosureProof.literalEmbeddingTypeClosure (Fin n) arity _ Gamma tau t hc).mpr
    intro u hu
    exact (sourceMembership s u).mpr (h.2 hu)
  have hsu := SourceUnmarkedProof.ordinaryEmbedding (Fin n) arity Gamma tau s
  have htu := SourceUnmarkedProof.ordinaryEmbedding (Fin n) arity Gamma tau t
  have hsh := NumberedFiniteUniverseProof.unmarkedHeadWindow (Fin n) arity (symbols n)
    (NumberedConfinedSourceSimulation.sourceWindow s) Gamma tau (embed s) hsu hs
    (NumberedOrdinaryWindowProof.allRanked _)
  have hth := NumberedFiniteUniverseProof.unmarkedHeadWindow (Fin n) arity (symbols n)
    (NumberedConfinedSourceSimulation.sourceWindow s) Gamma tau (embed t) htu ht
    (NumberedOrdinaryWindowProof.allRanked _)
  refine ⟨hc, ⟨hs, hsh⟩, ⟨ht, hth⟩, ?_, ?_⟩
  · exact NumberedFiniteUniverseProof.unmarkedUniverse (Fin n) arity (symbols n)
      (NumberedConfinedSourceSimulation.sourceWindow s) 0 Gamma tau (embed s)
      (translateOriginal s) hsu hs (NumberedOrdinaryWindowProof.allRanked _)
      (NumberedOrdinaryWindowProof.translationRepresentation 0 s)
  · exact NumberedFiniteUniverseProof.unmarkedUniverse (Fin n) arity (symbols n)
      (NumberedConfinedSourceSimulation.sourceWindow s) 0 Gamma tau (embed t)
      (translateOriginal t) htu ht (NumberedOrdinaryWindowProof.allRanked _)
      (NumberedOrdinaryWindowProof.translationRepresentation 0 t)

theorem strictWindowTrace : NumberedConfinedSourceSimulationTargets.ActualStrictWindowTrace := by
  intro n arity above Gamma tau s t h
  obtain ⟨hc, _, ht, hS, _⟩ := sourceWindow n arity above Gamma tau s t h
  obtain ⟨B, hB⟩ := NumberedWindowSimulationProof.strictSimulation (Fin n) arity
    (symbols n) (NumberedConfinedSourceSimulation.sourceWindow s) above hc Gamma
    ⟨tau, embed s⟩ ⟨tau, embed t⟩ h.1
  obtain ⟨count, hpos, path⟩ := hB (translateOriginal s)
    (NumberedOrdinaryWindowProof.translationRepresentation B s) hS ht
  exact ⟨count, hpos, path,
    NumberedWindowTracesProof.allBoundaries (Fin n) arity (symbols n)
      (NumberedConfinedSourceSimulation.sourceWindow s) hc above Gamma count
      (translated s) (translated t) path hS⟩

theorem strictQuotientPath : NumberedConfinedSourceSimulationTargets.ActualStrictQuotientPath := by
  intro n arity above Gamma tau s t h
  obtain ⟨hc, _, _, hS, _⟩ := sourceWindow n arity above Gamma tau s t h
  obtain ⟨count, hpos, path, _⟩ := strictWindowTrace n arity above Gamma tau s t h
  apply (NumberedQuotientPathsProof.positiveClosure n arity (symbols n)
    (NumberedConfinedSourceSimulation.sourceWindow s) above Gamma _ _).mpr
  refine ⟨count, hpos, ?_⟩
  exact NumberedQuotientPathsProof.countedForward n arity (symbols n)
    (NumberedConfinedSourceSimulation.sourceWindow s) hc above Gamma count
    (translated s) (translated t) hS path

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedConfinedSourceSimulationProof
