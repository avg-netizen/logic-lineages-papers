module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentExchangeLayer.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeAnswerSlots.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeLayer.LambdaProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentExchangeLayer.InternalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalAcceptanceBranchProof
open InternalGraphCompositionFunctionalityProof InternalTagArithmeticSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn sucRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {bodyFormula : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem optionalValue (U : Fin 19 → Program 3) (V : Program 3)
    (node code param out : OTerm alpha) (xs : Fin 19 → OTerm alpha)
    (hV : Nonempty (Derivation bodyFormula Delta (graph3 V (numeral 1) node code param)))
    (hs : ∀ i, Nonempty (Derivation bodyFormula Delta (graph3 (fields U i) (xs i) node code param)))
    (hl : Nonempty (Derivation bodyFormula Delta (programGraph ExchangeLayer.layer out xs))) :
    Nonempty (Derivation bodyFormula Delta (graph3 (optional U V) (suc out) node code param)) := by
  let v : Fin 3 → OTerm alpha := ![node,code,param]
  have hb : Nonempty (Derivation bodyFormula Delta (programGraph (body U) out v)) :=
    compositionValue ExchangeLayer.layer (fields U) out v xs hl hs
  have ho := unaryValue .succ (body U) (suc out) out v
    (successorValue (Fin.cons out Fin.elim0)) hb
  exact successorBranchIntro V (InternalLessThan.constantOne 3) _ (suc out) z v hV ho

theorem internalBodyFactor : Targets.InternalBodyFactor := by
  intro bodyFormula alpha Delta U V node code param out xs hV hs
  constructor
  · intro ho
    apply programCases ExchangeLayer.layer xs _
    intro beta j Theta value hj hv
    rw [programRename]
    have hV' := renameInto hV j Theta hj
    rw [graph3Rename] at hV'
    have hs' (i : Fin 19) : Nonempty (Derivation bodyFormula Theta
        (graph3 (fields U i) ((xs i).relabel j) (node.relabel j) (code.relabel j) (param.relabel j))) := by
      have h := renameInto (hs i) j Theta hj
      simpa only [graph3Rename] using h
    have ho' := renameInto ho j Theta hj
    simp only [graph3Rename,sucRelabel] at ho'
    have hn := optionalValue U V (node.relabel j) (code.relabel j) (param.relabel j)
      value (fun i => (xs i).relabel j) hV' hs' hv
    obtain ⟨he⟩ := valueUnique (optional U V) (suc value) (suc (out.relabel j))
      ![node.relabel j,code.relabel j,param.relabel j] hn ho'
    exact outputTransport ExchangeLayer.layer value (out.relabel j) (fun i => (xs i).relabel j)
      ⟨cancelSuc he⟩ hv
  · exact optionalValue U V node code param out xs hV hs

theorem internalLambda : Targets.InternalLambda := by
  intro bodyFormula alpha Delta U V node code param head tail xs hV hs hx hy hc
  have hf := internalBodyFactor bodyFormula alpha Delta U V node code param (numeral 1) xs hV hs
  have hl := ExchangeLayer.LambdaProof.internalLambda bodyFormula alpha Delta xs hx hy
  have ha : Nonempty (Derivation bodyFormula Delta
      (graph3 (ExchangeAnswerSlots.answer 0) (xs 14) node code param)) := by
    simpa only [fields,ite_true] using hs 14
  have hslot := ExchangeAnswerSlots.InternalProof.internalLeft bodyFormula alpha Delta node code param head tail hc
  constructor
  · intro h
    obtain ⟨hh⟩ := hl.mp (hf.mp h)
    have hv := outputTransport (ExchangeAnswerSlots.answer 0) (xs 14) (numeral 1) ![node,code,param]
      ⟨Derivation.conjunctionRight hh⟩ ha
    obtain ⟨he⟩ := hslot.mp hv
    exact ⟨Derivation.conjunctionIntroduction (Derivation.conjunctionLeft hh) he⟩
  · rintro ⟨h⟩
    have hv := hslot.mpr ⟨Derivation.conjunctionRight h⟩
    obtain ⟨he⟩ := valueUnique (ExchangeAnswerSlots.answer 0) (xs 14) (numeral 1) ![node,code,param] ha hv
    exact hf.mpr (hl.mpr ⟨Derivation.conjunctionIntroduction (Derivation.conjunctionLeft h) he⟩)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentExchangeLayer.InternalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentExchangeLayer.InternalProof
