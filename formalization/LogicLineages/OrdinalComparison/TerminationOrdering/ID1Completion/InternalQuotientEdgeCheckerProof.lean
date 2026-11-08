module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientEdgeCheckerSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientEdgeCheckerProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalQuotientEdgeChecker InternalQuotientEdgeCheckerSupportProof
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsProof InternalControlGraphSupportProof

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem checkerRecoverAtValues (data : Data) (x y certificate s t k sv tv : OTerm α)
    (hp : Nonempty (Derivation body Gamma (valuePremises data certificate s t k sv tv)))
    (hc : Nonempty (Derivation body Gamma (accepted data x y certificate))) :
    Nonempty (Derivation body Gamma (valueRequirements data x y s t k sv tv)) := by
  obtain ⟨hp⟩ := hp
  obtain ⟨hr⟩ := checkerRecover data x y certificate s t k ⟨Derivation.conjunctionLeft hp⟩ hc
  obtain ⟨hs⟩ := valueUnique data.sourceRepresentative sv x (Fin.cons s Fin.elim0)
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight hp)⟩
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight hr)⟩
  obtain ⟨ht⟩ := valueUnique data.targetRepresentative tv y (Fin.cons t Fin.elim0)
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight hp)⟩
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight hr)⟩
  simp only [valueRequirements,equalEqn]
  exact ⟨Derivation.conjunctionIntroduction (Derivation.conjunctionLeft hr)
    (Derivation.conjunctionIntroduction hs ht)⟩

theorem checkerAcceptAtValues (data : Data) (x y certificate s t k sv tv : OTerm α)
    (hp : Nonempty (Derivation body Gamma (valuePremises data certificate s t k sv tv)))
    (hr : Nonempty (Derivation body Gamma (valueRequirements data x y s t k sv tv))) :
    Nonempty (Derivation body Gamma (accepted data x y certificate)) := by
  obtain ⟨hp⟩ := hp
  obtain ⟨hr⟩ := hr
  simp only [valueRequirements,equalEqn] at hr
  obtain ⟨hs⟩ := outputTransport data.sourceRepresentative sv x (Fin.cons s Fin.elim0)
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight hr)⟩
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight hp)⟩
  obtain ⟨ht⟩ := outputTransport data.targetRepresentative tv y (Fin.cons t Fin.elim0)
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight hr)⟩
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight hp)⟩
  exact checkerAccept data x y certificate s t k ⟨Derivation.conjunctionLeft hp⟩
    ⟨Derivation.conjunctionIntroduction (Derivation.conjunctionLeft hr)
      (Derivation.conjunctionIntroduction hs ht)⟩

theorem actualOriginalAcceptanceEquation :
    InternalQuotientEdgeCheckerTargets.ActualOriginalAcceptanceEquation := by
  intro body data α x y certificate s t k
  apply guardedIff
  · exact checkerRecover data x y certificate s t k
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩
  · exact checkerAccept data x y certificate s t k
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩

theorem actualOriginalAcceptanceAtValues :
    InternalQuotientEdgeCheckerTargets.ActualOriginalAcceptanceAtValues := by
  intro body data α x y certificate s t k sv tv
  apply guardedIff
  · exact checkerRecoverAtValues data x y certificate s t k sv tv
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩
  · exact checkerAcceptAtValues data x y certificate s t k sv tv
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩

theorem actualOriginalEncodedAcceptanceEquation :
    InternalQuotientEdgeCheckerTargets.ActualOriginalEncodedAcceptanceEquation := by
  intro body data α x y certificate s t k
  apply guardedIff
  · exact checkerRecover data x y certificate s t k
      (edgeSelectors certificate s t k
        ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩)
      ⟨Derivation.hypothesis List.mem_cons_self⟩
  · exact checkerAccept data x y certificate s t k
      (edgeSelectors certificate s t k
        ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩)
      ⟨Derivation.hypothesis List.mem_cons_self⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientEdgeCheckerProof
