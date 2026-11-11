module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderStepSpecification
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderStepSpecification
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors (graph2)
open InternalGraphComposition (OTerm)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalTypedDecoderStepSpecification
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The root condition uses only arithmetic fields, exact-one membership and
local head-window graphs. Gamma does not occur. The numbered head is distinct
from both its recorded result and the head signature's result. -/
def guardCondition {alpha : Type} (M W : Program 2)
    (mode typ tag domain numberedHead context : OTerm alpha) : Formula alpha :=
  (equal mode (numeral 0) ⊓
    (graph2 M (numeral 1) typ context ⊓
      ((equal tag (numeral 1) ⊓ graph2 M (numeral 1) domain context) ⊔
        ((equal tag (numeral 4) ⊓ graph2 W (numeral 1) domain context) ⊔
          ((equal tag (numeral 5) ⊓ graph2 W (numeral 1) numberedHead context) ⊔
            ((equal tag (numeral 1)).not ⊓
              ((equal tag (numeral 4)).not ⊓ (equal tag (numeral 5)).not))))))) ⊔
    equal mode (numeral 1)

/-- Open the literal request and raw payload prefix through ORIGINAL pair
relations. No graph of the new guard or transition occurs on this side. -/
def guardSpec {alpha : Type} (M W : Program 2)
    (out request context : OTerm alpha) : Formula alpha :=
  let v : Fin 10 → OTerm (alpha ⊕ Fin 10) := fun i => .var (.inr i)
  let condition := guardCondition M W (v 0) (v 2) (v 4) (v 6) (v 8)
    (context.relabel Sum.inl)
  InternalFiniteBlocks.block (k := 10)
    (StepRequest (request.relabel Sum.inl) (v 0) (v 1) (v 2) (v 3) ⊓
      (StepPair (v 3) (v 4) (v 5) ⊓
        (StepPair (v 5) (v 6) (v 7) ⊓
          (StepPair (v 7) (v 8) (v 9) ⊓
            ((condition ⊓ equal (out.relabel Sum.inl) (numeral 1)) ⊔
              (condition.not ⊓ equal (out.relabel Sum.inl) (numeral 0)))))))

/-- Original worklist cons exposes the SAME request and suffix. A successful
local guard invokes the OLD independent typed one-step specification at the
SAME state; its failure returns zero. This is not a graph alias. -/
def nonemptySpec {alpha : Type} (H : Program 1) (M W : Program 2)
    (out input work context : OTerm alpha) : Formula alpha :=
  let v : Fin 2 → OTerm (alpha ⊕ Fin 2) := fun i => .var (.inr i)
  let accepted := guardSpec M W (numeral 1) (v 0) (context.relabel Sum.inl)
  InternalFiniteBlocks.block (k := 2)
    (StepCons (work.relabel Sum.inl) (v 0) (v 1) ⊓
      ((accepted ⊓ OriginalTypedDecoderStepSpecification.stepSpec H
          (out.relabel Sum.inl) (input.relabel Sum.inl)) ⊔
        (accepted.not ⊓ equal (out.relabel Sum.inl) (numeral 0))))

/-- Independent all-input and all-output arithmetic guarded one-step law.
No native calibration, decoded object, successful run or extra premise. -/
def stepSpec {alpha : Type} (H : Program 1) (M W : Program 2)
    (out input context : OTerm alpha) : Formula alpha :=
  let v : Fin 2 → OTerm (alpha ⊕ Fin 2) := fun i => .var (.inr i)
  InternalFiniteBlocks.block (k := 2)
    (StepPair (input.relabel Sum.inl) (v 0) (v 1) ⊓
      (((equal (v 0) (numeral 1)).not ⊓ equal (out.relabel Sum.inl) (numeral 0)) ⊔
        (equal (v 0) (numeral 1) ⊓
          ((equal (v 1) (numeral 0) ⊓ equal (out.relabel Sum.inl) (input.relabel Sum.inl)) ⊔
            ((equal (v 1) (numeral 0)).not ⊓
              nonemptySpec H M W (out.relabel Sum.inl) (input.relabel Sum.inl)
                (v 1) (context.relabel Sum.inl))))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderStepSpecification
