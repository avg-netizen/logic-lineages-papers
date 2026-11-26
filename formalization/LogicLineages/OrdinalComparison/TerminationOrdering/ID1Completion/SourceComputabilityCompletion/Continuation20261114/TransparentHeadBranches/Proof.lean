module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentHeadBranches.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentExchangeLayer.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeLayer.ApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentHeadBranches.FactorsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentHeadBranches.Proof
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

theorem identityImp (A : Formula alpha) : Nonempty (Derivation body Delta (A.imp A)) :=
  ⟨Derivation.implicationIntroduction (Derivation.hypothesis List.mem_cons_self)⟩

theorem andImp {A B C D : Formula alpha}
    (hf : Nonempty (Derivation body Delta (A.imp C)))
    (hg : Nonempty (Derivation body Delta (B.imp D))) :
    Nonempty (Derivation body Delta ((A ⊓ B).imp (C ⊓ D))) := by
  obtain ⟨hf⟩ := withHyp hf (A ⊓ B)
  obtain ⟨hg⟩ := withHyp hg (A ⊓ B)
  have h : Derivation body ((A ⊓ B) :: Delta) (A ⊓ B) := Derivation.hypothesis List.mem_cons_self
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationElimination hf (Derivation.conjunctionLeft h))
    (Derivation.implicationElimination hg (Derivation.conjunctionRight h)))⟩

theorem orImp {A B C D : Formula alpha}
    (hf : Nonempty (Derivation body Delta (A.imp C)))
    (hg : Nonempty (Derivation body Delta (B.imp D))) :
    Nonempty (Derivation body Delta ((A ⊔ B).imp (C ⊔ D))) := by
  obtain ⟨hf⟩ := withHyp (withHyp hf (A ⊔ B)) A
  obtain ⟨hg⟩ := withHyp (withHyp hg (A ⊔ B)) B
  have h : Derivation body ((A ⊔ B) :: Delta) (A ⊔ B) := Derivation.hypothesis List.mem_cons_self
  exact ⟨Derivation.implicationIntroduction (disjunctionElimination h
    (Derivation.implicationIntroduction (orLeft (Derivation.implicationElimination hf (Derivation.hypothesis List.mem_cons_self))))
    (Derivation.implicationIntroduction (orRight (Derivation.implicationElimination hg (Derivation.hypothesis List.mem_cons_self)))))⟩

theorem applyImp {A B : Formula alpha}
    (hf : Nonempty (Derivation body Delta (A.imp B)))
    (ha : Nonempty (Derivation body Delta A)) : Nonempty (Derivation body Delta B) := by
  obtain ⟨hf⟩ := hf
  obtain ⟨ha⟩ := ha
  exact ⟨Derivation.implicationElimination hf ha⟩

theorem internalOrdinary : Targets.InternalOrdinary := by
  intro body alpha Delta U V node code param h0 t0 xs hV hs hx hy hc0
  have hf := TransparentExchangeLayer.InternalProof.internalBodyFactor body alpha Delta U V node code param (numeral 1) xs hV hs
  have hl := (FactorsProof.dispatchOrdinary Delta xs hx hy).trans (FactorsProof.ordinaryFactor xs Delta)
  have ha0 : Nonempty (Derivation body Delta (graph3 (ExchangeAnswerSlots.answer 0) (xs 14) node code param)) := by
    simpa only [TransparentExchangeLayer.fields,ite_true] using hs 14
  let X := eqn (xs 14) (numeral 1)
  let X' := eqn h0 (numeral 1)
  have f0 : Nonempty (Derivation body Delta (X.imp X')) := by
    have hv := outputTransport (ExchangeAnswerSlots.answer 0) (xs 14) (numeral 1) ![node,code,param]
      (body:=body) (Gamma:=X :: Delta) ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp ha0 X)
    obtain ⟨he⟩ := (ExchangeAnswerSlots.InternalProof.internalLeft body alpha (X :: Delta)
      node code param h0 t0 (withHyp hc0 X)).mp hv
    exact ⟨Derivation.implicationIntroduction he⟩
  have r0 : Nonempty (Derivation body Delta (X'.imp X)) := by
    have hv := (ExchangeAnswerSlots.InternalProof.internalLeft body alpha (X' :: Delta)
      node code param h0 t0 (withHyp hc0 X')).mpr ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨he⟩ := valueUnique (ExchangeAnswerSlots.answer 0) (xs 14) (numeral 1) ![node,code,param] (withHyp ha0 X') hv
    exact ⟨Derivation.implicationIntroduction he⟩
  constructor
  · intro h
    exact applyImp (orImp (identityImp _) (andImp (identityImp _) f0)) (hl.mp (hf.mp h))
  · intro h
    exact hf.mpr (hl.mpr (applyImp (orImp (identityImp _) (andImp (identityImp _) r0)) h))

theorem internalNumbered : Targets.InternalNumbered := by
  intro body alpha Delta U V node code param h0 t0 h1 t1 h2 t2 h3 t3 xs hV hs hx hy hc0 hc1 hc2 hc3
  have hf := TransparentExchangeLayer.InternalProof.internalBodyFactor body alpha Delta U V node code param (numeral 1) xs hV hs
  have hl := (FactorsProof.dispatchNumbered Delta xs hx hy).trans (FactorsProof.numberedFactor xs Delta)
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
    exact applyImp (andImp (identityImp _)
      (orImp (orImp (identityImp _) (andImp (identityImp _) f0)) (andImp (identityImp _) f3))) (hl.mp (hf.mp h))
  · intro h
    exact hf.mpr (hl.mpr (applyImp (andImp (identityImp _)
      (orImp (orImp (identityImp _) (andImp (identityImp _) r0)) (andImp (identityImp _) r3))) h))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentHeadBranches.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentHeadBranches.Proof
