module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOrdinaryWindowTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOrdinaryWindowProof
open Source Source.SourceMarkedSyntax Source.SourcePortContexts Source.SourceTypeSupport NumberedRewriteSyntax NumberedRewriteReduction NumberedWindowCertificates NumberedFiniteUniverse NumberedWindowTraces NumberedOrdinaryWindow

theorem windowMembership {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty} {sigma tau : Ty}
    (s : Term (Fin n) arity Gamma sigma) (t : Term (Fin n) arity Gamma tau) (u : Ty) :
    u∈typeWindow s t ↔ u∈FiniteQueryPrimitives.inputTypes s t := by
  simp only [typeWindow,List.mem_append,FiniteQueryPrimitives.inputTypes,Finset.mem_union,
    ← SourcePortContextsProof.literalTypeEnumeration (Fin n) arity Gamma sigma s,
    ← SourcePortContextsProof.literalTypeEnumeration (Fin n) arity Gamma tau t,List.mem_toFinset]

theorem allRanked {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty} {tau : Ty}
    (q : MarkedTerm (Fin n) arity Gamma tau) : headsAllowed (RankedCovered (symbols n)) q := by
  apply (FiniteQueryPrimitivesProof.literalHeadCalibration (Fin n) arity Gamma tau q _).mpr
  intro f hf
  cases f <;> simp [RankedCovered,symbols]

theorem translationRepresentation {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty} {tau : Ty}
    (B : Nat) (q : Term (Fin n) arity Gamma tau) :
    Represents (Fin n) arity B Gamma tau (embed q) (translateOriginal q) := by
  have h := NumberedRewriteSyntaxProof.canonicalNumbering (Fin n) arity B Gamma tau (embed q)
  have he := NumberedRepresentationRigidityProof.unmarkedRepresentation (Fin n) arity B Gamma tau
    (embed q) (canonical B (embed q)) (SourceUnmarkedProof.ordinaryEmbedding (Fin n) arity Gamma tau q) h
  rw [he] at h
  exact h

theorem sourceWindow : NumberedOrdinaryWindowTargets.ActualSourceWindow := by
  intro n arity above Gamma sigma tau s t
  have hc : SubtypeClosed (fun u => u∈typeWindow s t) := by
    intro u hu v hv
    exact (windowMembership s t v).mpr ((FiniteQueryPrimitivesProof.initialFrame (Fin n) arity Gamma sigma tau s t).1 u
      ((windowMembership s t u).mp hu) v hv)
  have hs : typesAllowed (fun u => u∈typeWindow s t) (embed s) := by
    apply (TypeClosureProof.literalEmbeddingTypeClosure (Fin n) arity _ Gamma sigma s hc).mpr
    intro u hu
    exact (windowMembership s t u).mpr (Finset.mem_union_left _ hu)
  have ht : typesAllowed (fun u => u∈typeWindow s t) (embed t) := by
    apply (TypeClosureProof.literalEmbeddingTypeClosure (Fin n) arity _ Gamma tau t hc).mpr
    intro u hu
    exact (windowMembership s t u).mpr (Finset.mem_union_right _ hu)
  have hsu := SourceUnmarkedProof.ordinaryEmbedding (Fin n) arity Gamma sigma s
  have htu := SourceUnmarkedProof.ordinaryEmbedding (Fin n) arity Gamma tau t
  have hsh := NumberedFiniteUniverseProof.unmarkedHeadWindow (Fin n) arity (symbols n) (typeWindow s t) Gamma sigma (embed s) hsu hs (allRanked _)
  have hth := NumberedFiniteUniverseProof.unmarkedHeadWindow (Fin n) arity (symbols n) (typeWindow s t) Gamma tau (embed t) htu ht (allRanked _)
  refine ⟨hc,⟨hs,hsh⟩,⟨ht,hth⟩,?_,?_⟩
  · exact NumberedFiniteUniverseProof.unmarkedUniverse (Fin n) arity (symbols n) (typeWindow s t) 0 Gamma sigma (embed s)
      (translateOriginal s) hsu hs (allRanked _) (translationRepresentation 0 s)
  · exact NumberedFiniteUniverseProof.unmarkedUniverse (Fin n) arity (symbols n) (typeWindow s t) 0 Gamma tau (embed t)
      (translateOriginal t) htu ht (allRanked _) (translationRepresentation 0 t)

theorem weakOrdinaryPath : NumberedOrdinaryWindowTargets.ActualWeakOrdinaryPath := by
  intro n arity above Gamma sigma tau s t h
  obtain ⟨hc,hs,ht,hS,hT⟩ := sourceWindow n arity above Gamma sigma tau s t
  obtain ⟨B,hB⟩ := NumberedWindowSimulationProof.weakSimulation (Fin n) arity (symbols n) (typeWindow s t) above hc Gamma _ _ h
  obtain ⟨m,hm⟩ := hB (translateOriginal s) (translationRepresentation B s) hS ht
  exact ⟨m,hm,NumberedWindowTracesProof.allBoundaries (Fin n) arity (symbols n) (typeWindow s t) hc above Gamma m _ _ hm hS⟩

theorem strictOrdinaryPath : NumberedOrdinaryWindowTargets.ActualStrictOrdinaryPath := by
  intro n arity above Gamma sigma tau s t h
  obtain ⟨hc,hs,ht,hS,hT⟩ := sourceWindow n arity above Gamma sigma tau s t
  obtain ⟨B,hB⟩ := NumberedWindowSimulationProof.strictSimulation (Fin n) arity (symbols n) (typeWindow s t) above hc Gamma _ _ h
  obtain ⟨m,hpos,hm⟩ := hB (translateOriginal s) (translationRepresentation B s) hS ht
  exact ⟨m,hpos,hm,NumberedWindowTracesProof.allBoundaries (Fin n) arity (symbols n) (typeWindow s t) hc above Gamma m _ _ hm hS⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOrdinaryWindowProof
