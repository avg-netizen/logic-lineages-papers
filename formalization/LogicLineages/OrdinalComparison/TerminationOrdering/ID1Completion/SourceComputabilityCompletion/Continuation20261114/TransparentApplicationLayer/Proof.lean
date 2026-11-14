module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentApplicationLayer.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentExchangeLayer.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeLayer.ApplicationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentApplicationLayer.Proof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalBetaTotalityProof InternalQuotientComparisonProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem mapBranches (A B C X Y X' Y' : Formula alpha)
    (hx : Nonempty (Derivation body Delta (X.imp X')))
    (hy : Nonempty (Derivation body Delta (Y.imp Y')))
    (h : Nonempty (Derivation body Delta (A ⊓ ((B ⊓ X) ⊔ (C ⊓ Y))))) :
    Nonempty (Derivation body Delta (A ⊓ ((B ⊓ X') ⊔ (C ⊓ Y')))) := by
  obtain ⟨h⟩ := h
  obtain ⟨hx⟩ := withHyp hx (B ⊓ X)
  obtain ⟨hy⟩ := withHyp hy (C ⊓ Y)
  have hl : Derivation body ((B ⊓ X) :: Delta) (B ⊓ X) := Derivation.hypothesis List.mem_cons_self
  have hr : Derivation body ((C ⊓ Y) :: Delta) (C ⊓ Y) := Derivation.hypothesis List.mem_cons_self
  exact ⟨Derivation.conjunctionIntroduction (Derivation.conjunctionLeft h)
    (disjunctionElimination (Derivation.conjunctionRight h)
      (Derivation.implicationIntroduction (orLeft (Derivation.conjunctionIntroduction
        (Derivation.conjunctionLeft hl) (Derivation.implicationElimination hx (Derivation.conjunctionRight hl)))))
      (Derivation.implicationIntroduction (orRight (Derivation.conjunctionIntroduction
        (Derivation.conjunctionLeft hr) (Derivation.implicationElimination hy (Derivation.conjunctionRight hr))))))⟩

theorem internalApplication : Targets.InternalApplication := by
  intro body alpha Delta U V node code param h0 t0 h1 t1 h2 t2 h3 t3 xs tag ht hV hs hx hy hc0 hc1 hc2 hc3
  have hf := TransparentExchangeLayer.InternalProof.internalBodyFactor body alpha Delta U V node code param (numeral 1) xs hV hs
  have hl := ExchangeLayer.ApplicationProof.internalApplication body alpha Delta xs tag ht hx hy
  have ha0 : Nonempty (Derivation body Delta (graph3 (ExchangeAnswerSlots.answer 0) (xs 14) node code param)) := by
    simpa only [TransparentExchangeLayer.fields,ite_true] using hs 14
  have ha3 : Nonempty (Derivation body Delta (graph3 (ExchangeAnswerSlots.answer 3) (xs 15) node code param)) := by
    simpa only [TransparentExchangeLayer.fields,show (15 : Fin 19) ≠ 14 by decide,ite_false,ite_true] using hs 15
  let X := eqn (xs 14) (numeral 1)
  let Y := eqn (xs 15) (numeral 1)
  let X' := eqn h0 (numeral 1)
  let Y' := eqn h3 (numeral 1)
  have f0 : Nonempty (Derivation body Delta (X.imp X')) := by
    have hv := outputTransport (ExchangeAnswerSlots.answer 0) (xs 14) (numeral 1) ![node,code,param]
      (body:=body) (Gamma:=X :: Delta) ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp ha0 X)
    obtain ⟨he⟩ := (ExchangeAnswerSlots.InternalProof.internalLeft body alpha (X :: Delta)
      node code param h0 t0 (withHyp hc0 X)).mp hv
    exact ⟨Derivation.implicationIntroduction he⟩
  have f3 : Nonempty (Derivation body Delta (Y.imp Y')) := by
    have hv := outputTransport (ExchangeAnswerSlots.answer 3) (xs 15) (numeral 1) ![node,code,param]
      (body:=body) (Gamma:=Y :: Delta) ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp ha3 Y)
    obtain ⟨he⟩ := (ExchangeAnswerSlots.InternalProof.internalRight body alpha (Y :: Delta)
      node code param h0 t0 h1 t1 h2 t2 h3 t3
      (withHyp hc0 Y) (withHyp hc1 Y) (withHyp hc2 Y) (withHyp hc3 Y)).mp hv
    exact ⟨Derivation.implicationIntroduction he⟩
  have r0 : Nonempty (Derivation body Delta (X'.imp X)) := by
    have hv := (ExchangeAnswerSlots.InternalProof.internalLeft body alpha (X' :: Delta)
      node code param h0 t0 (withHyp hc0 X')).mpr ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨he⟩ := valueUnique (ExchangeAnswerSlots.answer 0) (xs 14) (numeral 1) ![node,code,param] (withHyp ha0 X') hv
    exact ⟨Derivation.implicationIntroduction he⟩
  have r3 : Nonempty (Derivation body Delta (Y'.imp Y)) := by
    have hv := (ExchangeAnswerSlots.InternalProof.internalRight body alpha (Y' :: Delta)
      node code param h0 t0 h1 t1 h2 t2 h3 t3
      (withHyp hc0 Y') (withHyp hc1 Y') (withHyp hc2 Y') (withHyp hc3 Y')).mpr ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨he⟩ := valueUnique (ExchangeAnswerSlots.answer 3) (xs 15) (numeral 1) ![node,code,param] (withHyp ha3 Y') hv
    exact ⟨Derivation.implicationIntroduction he⟩
  constructor
  · intro h
    exact mapBranches _ _ _ X Y X' Y' f0 f3 (hl.mp (hf.mp h))
  · intro h
    exact hf.mpr (hl.mpr (mapBranches _ _ _ X' Y' X Y r0 r3 h))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentApplicationLayer.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentApplicationLayer.Proof
