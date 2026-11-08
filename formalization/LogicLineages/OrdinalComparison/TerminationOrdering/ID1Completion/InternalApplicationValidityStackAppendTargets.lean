module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationValidityStackAppend
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Exact full-output nil equation for the explicit original-code append AST. -/
def ActualOriginalRawListAppendZero : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type)
    (out suffix : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body []
    ((graph2 append out OrdinaryArithmetic.zeroTerm suffix).iff (equal out suffix)))

/-- Exact full-output cons equation, assuming only the original constructor
graph. The internally quantified recursive output is not supplied externally. -/
def ActualOriginalRawListAppendCons : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type)
    (frontWork head tail suffix out : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body []
    ((graph2 InternalListCodec.consCode frontWork head tail).imp
      ((graph2 append out frontWork suffix).iff (appendConsStep out head tail suffix))))

/-- Truthful sequential success composition for the ACTUAL frozen stack
transition and arbitrary original unary Program guards. The prefix need not
use all of its fuel: once it finishes, the attached suffix may begin early.
Only success at the summed count is concluded, not equality of intermediate
states at the first count. Every count and raw list code is symbolic, and no
decoder, external calibration, validity closure or weight bound is assumed. -/
def ActualOriginalSuccessfulWorkAppend : Prop :=
  ∀ (body : Positive (Fin 1)) (node leaf : Program 1) (α : Type)
    (first second frontWork suffix joined : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body []
    ((graph2 append joined frontWork suffix ⊓
      (successfulWork node leaf first frontWork ⊓ successfulWork node leaf second suffix)).imp
      (successfulWork node leaf (OrdinaryArithmetic.addTerm first second) joined)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendTargets
