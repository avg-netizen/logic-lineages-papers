module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceSimulationCompletionFixedWindowTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceSimulationCompletionFixedWindowProof
open Source Source.SourceMarkedSyntax Source.SourceTypeSupport
open NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse
open NumberedWindowCertificates NumberedWindowTraces NumberedOrdinaryWindow
open NumberedLeastCodeRepresentative NumberedQuotientPaths NumberedConfinedSourceSimulation
open LiteralContexts SourceSimulationCompletion SourceSimulationCompletionFixedWindowTargets

theorem anyFixedUniverseSimulation : AnyFixedUniverseSimulation := by
  intro n arity above Gamma S hc tau s t hs h
  have hst : typesAllowed (fun u => u ∈ S) (embed s) :=
    (TypeClosureProof.literalEmbeddingTypeClosure (Fin n) arity _ Gamma tau s hc).mpr hs
  have htt : typesAllowed (fun u => u ∈ S) (embed t) :=
    (TypeClosureProof.literalEmbeddingTypeClosure (Fin n) arity _ Gamma tau t hc).mpr
      (fun u hu => hs u (h.2 hu))
  have hsu := SourceUnmarkedProof.ordinaryEmbedding (Fin n) arity Gamma tau s
  have htu := SourceUnmarkedProof.ordinaryEmbedding (Fin n) arity Gamma tau t
  have hS : InUniverse (symbols n) S (translateOriginal s) :=
    NumberedFiniteUniverseProof.unmarkedUniverse (Fin n) arity (symbols n) S 0
      Gamma tau (embed s) (translateOriginal s) hsu hst
      (NumberedOrdinaryWindowProof.allRanked _)
      (NumberedOrdinaryWindowProof.translationRepresentation 0 s)
  have hT : InUniverse (symbols n) S (translateOriginal t) :=
    NumberedFiniteUniverseProof.unmarkedUniverse (Fin n) arity (symbols n) S 0
      Gamma tau (embed t) (translateOriginal t) htu htt
      (NumberedOrdinaryWindowProof.allRanked _)
      (NumberedOrdinaryWindowProof.translationRepresentation 0 t)
  have htGood : OriginalGood (symbols n) S ⟨tau,embed t⟩ :=
    ⟨htt, NumberedFiniteUniverseProof.unmarkedHeadWindow (Fin n) arity (symbols n)
      S Gamma tau (embed t) htu htt (NumberedOrdinaryWindowProof.allRanked _)⟩
  obtain ⟨B, hB⟩ := NumberedWindowSimulationProof.strictSimulation (Fin n) arity
    (symbols n) S above hc Gamma ⟨tau,embed s⟩ ⟨tau,embed t⟩ h.1
  obtain ⟨count, hpos, path⟩ := hB (translateOriginal s)
    (NumberedOrdinaryWindowProof.translationRepresentation B s) hS htGood
  refine ⟨hS, hT, ?_⟩
  apply (NumberedQuotientPathsProof.positiveClosure n arity (symbols n) S above
    Gamma _ _).mpr
  refine ⟨count, hpos, ?_⟩
  exact NumberedQuotientPathsProof.countedForward n arity (symbols n) S hc above
    Gamma count (translated s) (translated t) hS path

private theorem sourceMembership {n : Nat} {arity : Fin n → Nat}
    {Gamma : List Ty} {tau : Ty} (s : Term (Fin n) arity Gamma tau) (u : Ty) :
    u ∈ sourceWindow s ↔ u ∈ typeSupport s := by
  simp only [sourceWindow,
    ← Source.SourcePortContextsProof.literalTypeEnumeration (Fin n) arity Gamma tau s,
    List.mem_toFinset]

theorem originalRootWindowSimulation : OriginalRootWindowSimulation := by
  intro n arity above Gamma rho tau root s t hs h
  have hc : SubtypeClosed (fun u => u ∈ sourceWindow root) := by
    intro u hu v hv
    exact (sourceMembership root v).mpr
      (SourceTypeSupportProof.subtypeClosedSupport (Fin n) arity Gamma rho root u
        ((sourceMembership root u).mp hu) v hv)
  exact anyFixedUniverseSimulation n arity above Gamma (sourceWindow root) hc tau s t
    (fun u hu => (sourceMembership root u).mpr (hs hu)) h

private theorem chainSupport {n : Nat} {arity : Fin n → Nat}
    {above : Fin n → Fin n → Prop} {Gamma : List Ty} {tau : Ty}
    {s t : Term (Fin n) arity Gamma tau}
    (path : Relation.TransGen (fun q r : Term (Fin n) arity Gamma tau =>
      ConfinedStrict above q r) s t) : typeSupport t ⊆ typeSupport s := by
  induction path with
  | single h => exact h.2
  | tail _ step ih => exact fun _ hu => ih (step.2 hu)

theorem originalRootWindowChainSimulation : OriginalRootWindowChainSimulation := by
  intro n arity above Gamma rho tau root s t hs path
  induction path with
  | single h =>
      exact (originalRootWindowSimulation n arity above Gamma rho tau root s _ hs h).2.2
  | @tail q r path step ih =>
      exact PositivePath.trans ih
        (originalRootWindowSimulation n arity above Gamma rho tau root q r
          (fun _ hu => hs (chainSupport path hu)) step).2.2

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceSimulationCompletionFixedWindowProof
