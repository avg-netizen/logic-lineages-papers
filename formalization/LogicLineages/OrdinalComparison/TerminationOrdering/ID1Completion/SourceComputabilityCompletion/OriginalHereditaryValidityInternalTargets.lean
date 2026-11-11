module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalHereditaryValidity OriginalHereditaryValidityInternal
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The live state's frame, raw value, own parameter and remaining work are
constructed internally and connected to their actual machine selectors. -/
def ActualOriginalHereditaryLiveWorkOpening : Prop := LiveWorkOpening

/-- Exact internal acceptance factorization for ARBITRARY original binary
leaves and every state. Only the actual current raw/parameter selector graphs
are supplied. Original type/tag witnesses are generated internally, both old
leaves accept one, and application membership uses the same original type
and parameter. This is independent of every native calibration theorem. -/
def ActualOriginalHereditaryNodeGraph : Prop :=
  ∀ (body : Positive (Fin 1)) (oldSource oldTarget member : Program 2)
    (alpha : Type) (state raw parameter : OTerm alpha),
  Nonempty (Derivation body []
    ((graph1 currentRaw raw state ⊓ graph1 currentParameter parameter state).imp
      ((graph1 (nodeCheck oldSource oldTarget member) (numeral 1) state).iff
        (NodeFactors oldSource oldTarget member raw parameter))))

/-- The original singleton initial AST, not a substituted state relation,
recovers the SAME original root raw/parameter leaf factors. No selector,
type, tag, frame or work witness is an external premise. This is a root NODE
law only: bounded validator acceptance-to-node acceptance remains pending. -/
def ActualOriginalHereditaryInitialNodeGraph : Prop :=
  ∀ (body : Positive (Fin 1)) (oldSource oldTarget member : Program 2)
    (alpha : Type) (state raw parameter : OTerm alpha),
  Nonempty (Derivation body []
    ((graph2 initial state raw parameter).imp
      ((graph1 (nodeCheck oldSource oldTarget member) (numeral 1) state).iff
        (NodeFactors oldSource oldTarget member raw parameter))))

/-- An accepting nonapplication/nonlambda pops exactly the SAME work tail.
The tag is obtained from the original raw value in the connected frame;
arbitrary other tags are allowed. Output is unrestricted, so this is a
full-output graph equation rather than a success-only implication. -/
def ActualOriginalHereditaryPopTransition : Prop :=
  ∀ (body : Positive (Fin 1)) (oldSource oldTarget member : Program 2)
    (alpha : Type) (state workCode frame raw parameter restCode tag out : OTerm alpha),
  Nonempty (Derivation body []
    ((StateFrame state workCode frame raw parameter restCode ⊓
      (graph1 (nodeCheck oldSource oldTarget member) (numeral 1) state ⊓
        (graph1 OriginalLambdaConstructor.tag tag raw ⊓
          ((equal tag (numeral 2)).not ⊓ (equal tag (numeral 1)).not)))).imp
      ((graph1 (transition oldSource oldTarget member) out state).iff
        (StateGraph out (numeral 1) restCode))))

/-- Acceptance opens the exact function and argument selectors, constructs
their pair-coded frames internally, and prepends both at the SAME parameter
and SAME rest. No child typing or child-validity hypothesis occurs. -/
def ActualOriginalHereditaryApplicationTransition : Prop :=
  ∀ (body : Positive (Fin 1)) (oldSource oldTarget member : Program 2)
    (alpha : Type) (state workCode frame raw parameter restCode out : OTerm alpha),
  Nonempty (Derivation body []
    ((StateFrame state workCode frame raw parameter restCode ⊓
      (graph1 (nodeCheck oldSource oldTarget member) (numeral 1) state ⊓
        graph1 OriginalLambdaConstructor.tag (numeral 2) raw)).imp
      ((graph1 (transition oldSource oldTarget member) out state).iff
        (ApplicationResult state out parameter restCode))))

/-- Acceptance opens the ACTUAL repacked body, internally reconstructs the
original parameter and its single domain/Gamma extension, and pushes that
body at the SAME rest. The original outer context is preserved. In particular,
source validity of the body is NOT a premise disguised as this conclusion. -/
def ActualOriginalHereditaryLambdaTransition : Prop :=
  ∀ (body : Positive (Fin 1)) (oldSource oldTarget member : Program 2)
    (alpha : Type) (state workCode frame raw parameter restCode out : OTerm alpha),
  Nonempty (Derivation body []
    ((StateFrame state workCode frame raw parameter restCode ⊓
      (graph1 (nodeCheck oldSource oldTarget member) (numeral 1) state ⊓
        graph1 OriginalLambdaConstructor.tag (numeral 1) raw)).imp
      ((graph1 (transition oldSource oldTarget member) out state).iff
        (LambdaResult state out raw parameter restCode))))

/-- Non-one status and a rejected node of an actual nonempty live state both
produce literal failure zero. This includes every non-Boolean leaf output;
neither a native result nor a supplied rejecting output is assumed. -/
def ActualOriginalHereditaryRejectTransition : Prop :=
  ∀ (body : Positive (Fin 1)) (oldSource oldTarget member : Program 2)
    (alpha : Type) (state out : OTerm alpha),
  Nonempty (Derivation body []
    (((graph1 status (numeral 1) state).not ⊔
      (LiveWork state ⊓ (graph1 (nodeCheck oldSource oldTarget member)
        (numeral 1) state).not)).imp
      ((graph1 (transition oldSource oldTarget member) out state).iff
        (equal out OrdinaryArithmetic.zeroTerm))))

/-- Failure zero is absorbing; status one with empty work is also absorbing
at its SAME state code. These are exact internal graph equations, not a
statement that an arbitrary bounded run has reached either endpoint. -/
def ActualOriginalHereditaryAbsorbingStates : Prop :=
  ∀ (body : Positive (Fin 1)) (oldSource oldTarget member : Program 2)
    (alpha : Type) (state out : OTerm alpha),
  Nonempty (Derivation body []
    ((graph1 (transition oldSource oldTarget member) out OrdinaryArithmetic.zeroTerm).iff
      (equal out OrdinaryArithmetic.zeroTerm))) ∧
  Nonempty (Derivation body []
    ((StateGraph state (numeral 1) OrdinaryArithmetic.zeroTerm).imp
      ((graph1 (transition oldSource oldTarget member) out state).iff (equal out state))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalTargets
