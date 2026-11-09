module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomParameterTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformDescentSelectionInternalProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomParameterInternalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceBranchProof
open InternalAcceptanceConjunctionProof (constantZeroValue)
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (OTerm z suc)
open InternalBetaTotalityProof (addHyp)
open SourceComputabilityCompletion.BottomParameter
open SourceComputabilityCompletion.BottomRepresentative (bottomTest bottomGraph)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem withHyp {phi : Formula α} (h : Nonempty (Derivation body Gamma phi)) (p : Formula α) :
    Nonempty (Derivation body (p :: Gamma) phi) := by
  obtain ⟨h⟩ := h
  exact ⟨addHyp h p⟩

theorem contextParameterValue (value parameter context gamma contextOnly : OTerm α)
    (hp : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing parameter context gamma)))
    (hz : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing contextOnly context z))) :
    Nonempty (Derivation body Gamma (graph2 contextParameter contextOnly value parameter)) := by
  let xs : Fin 2 → OTerm α := ![value,parameter]
  exact binaryValue InternalPairing.pairing (leftOf (.projection 1)) (InternalAcceptance.constantZero 2)
    contextOnly context z xs hz
    (unaryValue InternalUnpair.left (.projection (1 : Fin 2)) context parameter xs
      (pairLeft parameter context gamma hp) (projectionValue 1 xs))
    (constantZeroValue xs)

theorem bottomControl (value parameter : OTerm α)
    (h : Nonempty (Derivation body Gamma (bottomGraph (suc z) value))) :
    Nonempty (Derivation body Gamma (graph2 exactBottom (suc z) value parameter)) :=
  unaryValue bottomTest (.projection (0 : Fin 2)) (suc z) value ![value,parameter]
    h (projectionValue 0 ![value,parameter])

theorem normalizedRecover (old : Program 2)
    (out value parameter context gamma contextOnly : OTerm α)
    (hp : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing parameter context gamma)))
    (hz : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing contextOnly context z)))
    (hb : Nonempty (Derivation body Gamma (bottomGraph (suc z) value)))
    (hn : Nonempty (Derivation body Gamma (graph2 (normalized old) out value parameter))) :
    Nonempty (Derivation body Gamma (graph2 old out value contextOnly)) := by
  let xs : Fin 2 → OTerm α := ![value,parameter]
  have hc := contextParameterValue value parameter context gamma contextOnly hp hz
  have ha := successorBranchElim exactBottom old (atContext old) out z xs
    (bottomControl value parameter hb) hn
  exact compositionRecover old ![.projection 0,contextParameter] out xs ![value,contextOnly]
    ha (fun i => Fin.cases (projectionValue 0 xs) (Fin.cases hc (fun k => Fin.elim0 k)) i)

theorem normalizedValue (old : Program 2)
    (out value parameter context gamma contextOnly : OTerm α)
    (hp : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing parameter context gamma)))
    (hz : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing contextOnly context z)))
    (hb : Nonempty (Derivation body Gamma (bottomGraph (suc z) value)))
    (ho : Nonempty (Derivation body Gamma (graph2 old out value contextOnly))) :
    Nonempty (Derivation body Gamma (graph2 (normalized old) out value parameter)) := by
  let xs : Fin 2 → OTerm α := ![value,parameter]
  have hc := contextParameterValue value parameter context gamma contextOnly hp hz
  have ha := compositionValue old ![.projection 0,contextParameter] out xs ![value,contextOnly]
    ho (fun i => Fin.cases (projectionValue 0 xs) (Fin.cases hc (fun k => Fin.elim0 k)) i)
  exact successorBranchIntro exactBottom old (atContext old) out z xs (bottomControl value parameter hb) ha

theorem actualParameterizedBottomLeafSlice : BottomParameterTargets.ActualParameterizedBottomLeafSlice := by
  intro body old α Delta out value parameter context gamma contextOnly
  let H := graph2 InternalPairing.pairing parameter context gamma ⊓
    graph2 InternalPairing.pairing contextOnly context z
  let B := bottomGraph (suc z) value
  let P := graph2 (normalized old) out value parameter
  let Q := graph2 old out value contextOnly
  have hh : Nonempty (Derivation body (B :: H :: Delta) H) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  have hb : Nonempty (Derivation body (B :: H :: Delta) B) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hf⟩ := normalizedRecover old out value parameter context gamma contextOnly
    (withHyp (andLeft hh) P) (withHyp (andRight hh) P) (withHyp hb P)
    (show Nonempty (Derivation body (P :: B :: H :: Delta) P) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hr⟩ := normalizedValue old out value parameter context gamma contextOnly
    (withHyp (andLeft hh) Q) (withHyp (andRight hh) Q) (withHyp hb Q)
    (show Nonempty (Derivation body (Q :: B :: H :: Delta) Q) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction
    (Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
      (Derivation.implicationIntroduction hr)))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomParameterInternalProof
