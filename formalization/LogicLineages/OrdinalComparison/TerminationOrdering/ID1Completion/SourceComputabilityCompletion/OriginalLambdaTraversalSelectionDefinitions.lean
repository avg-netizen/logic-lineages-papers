module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalSelection
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalOriginalUniformDescentSelection (Data)
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The original validity leaves are made transparent ONCE. This data has
no reference to the traversal, its prepared representative or its final tuple. -/
def transparentData (rawData : Data) : Data :=
  OriginalTransparentLambdaValidity.refineData rawData

/-- Exact previously accepted selection at the once-transparent data. This
is solely the finite acyclic supplier of the OTHER-TAG leaf. It is not the
eventual final Data and cannot substitute for a SAME-final body theorem. -/
def leafData (rawData : Data) (window : Program 1) : Data :=
  OriginalApplicationSidecar.selectedData (transparentData rawData) window

def leaf (rawData : Data) (window : Program 1) : Program 2 :=
  InternalParameterizedCanonicalResultFold.leaf (leafData rawData window)

/-- C opens ALL raw application/lambda tags, rebuilds the original raw
constructors, and uses the prior selected leaf only at OTHER tags. Every
lambda visit changes its own actual encoded Gamma, not a global parameter. -/
def canonical (rawData : Data) (window : Program 1) : Program 2 :=
  OriginalLambdaTraversal.fold (leaf rawData window)

/-- Keep the WHOLE literal old representative on inactive inputs. In
particular raw malformed inputs, source-invalid decoded terms and nonclosed
windows are not silently assigned the unguarded traversal output. All-input
calibration of the active branch is an obligation, never a definition. -/
def representative (rawData : Data) (window : Program 1) : Program 2 :=
  InternalAcceptance.branch
    (OriginalFunctionNeutrality.active (transparentData rawData) window)
    rawData.oldRepresentative (canonical rawData window)

def preparedData (rawData : Data) (window : Program 1) : Data :=
  { transparentData rawData with oldRepresentative := representative rawData window }

def prepareInputs (p : GlobalSourcePackage.Inputs) : GlobalSourcePackage.Inputs :=
  { p with base := preparedData p.base p.window }

/-- The ENTIRE existing hereditary/global final pipeline is applied after
preparation. No accepted source, typed checker, actualJ, quotient edge, step
guard or application-only final canonical fold is replaced by C. -/
def finalInputs (p : GlobalSourcePackage.Inputs) : GlobalSourcePackage.Inputs :=
  OriginalHereditaryLambdaGlobal.finalInputs (prepareInputs p)

def finalData (p : GlobalSourcePackage.Inputs) : Data :=
  OuterSelection.data (finalInputs p).base (finalInputs p).window

/-- Supporting output facts to prove about C. Source validity, type and
nonincrease are accompanied by genuine C-idempotence of its actual output.
None is stored in the Program tuple or assumed by a final coherence law. -/
def OutputInvariant {alpha : Type} (rawData : Data) (window : Program 1)
    (out input typ parameter : OTerm alpha) : Formula alpha :=
  graph2 (InternalOriginalUniformDescentSelection.validity (leafData rawData window))
      InternalOriginalStepGuard.one out parameter ⊓
    (graph1 InternalUnpair.left typ out ⊓
      (InternalParameterizedBoundedDescentNormalizer.atMost out input ⊓
        graph2 (canonical rawData window) out out parameter))

def OutputLaws (rawData : Data) (window : Program 1) : Prop :=
  ∀ (positive : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (out input typ parameter : OTerm alpha),
  Nonempty (Derivation positive Delta
    ((OriginalFunctionNeutrality.windowGraph window input parameter ⊓
      (InternalParameterizedCanonicalResultFold.sourcePremises
        (leafData rawData window) input typ parameter ⊓
        graph2 (canonical rawData window) out input parameter)).imp
      (OutputInvariant rawData window out input typ parameter)))

def PreservesObserver (rawData : Data) (window observer : Program 1) : Prop :=
  ∀ (positive : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (out input typ parameter mark : OTerm alpha),
  Nonempty (Derivation positive Delta
    ((OriginalFunctionNeutrality.windowGraph window input parameter ⊓
      (InternalParameterizedCanonicalResultFold.sourcePremises
        (leafData rawData window) input typ parameter ⊓
        graph2 (canonical rawData window) out input parameter)).imp
      ((graph1 observer mark out).iff (graph1 observer mark input))))

/-- The actual existing guard observers, not newly designed properties
chosen to make the conclusion true. Their internal redundancy is needed
before passing C through the whole unchanged representative pipeline. -/
def ObserverLaws (rawData : Data) (window : Program 1) : Prop :=
  PreservesObserver rawData window OriginalConstructorShape.mark ∧
    PreservesObserver rawData window OriginalVariableRepresentative.variableMark ∧
    PreservesObserver rawData window OriginalFunctionNeutrality.mark ∧
    PreservesObserver rawData window BottomSpineMeasure.measure ∧
    PreservesObserver rawData window BottomRepresentative.bottomTest

/-- Bidirectional identification of the ACTUAL final bounded-descent
transition with C under the original final source/window/type graphs. This
is an internal theorem obligation, not reflection from native equality. -/
def FinalTransitionLaw (p : GlobalSourcePackage.Inputs) : Prop :=
  ∀ (positive : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (out input typ parameter : OTerm alpha),
  Nonempty (Derivation positive Delta
    ((OriginalFunctionNeutrality.windowGraph (finalInputs p).window input parameter ⊓
      InternalParameterizedCanonicalResultFold.sourcePremises
        (finalData p) input typ parameter).imp
      ((InternalParameterizedBoundedDescentNormalizer.transitionGraph
        (finalData p).oldRepresentative
        (InternalOriginalUniformDescentSelection.validity (finalData p))
        out input parameter).iff
        (graph2 (canonical p.base p.window) out input parameter))))

/-- Identify the actual unchanged final application-only canonical fold
with C at its valid original inputs. No C equality, child fixedness, final
leaf identity or successful child run is assumed as an arithmetic premise. -/
def FinalCanonicalLaw (p : GlobalSourcePackage.Inputs) : Prop :=
  ∀ (positive : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (out input typ parameter : OTerm alpha),
  Nonempty (Derivation positive Delta
    ((OriginalFunctionNeutrality.windowGraph (finalInputs p).window input parameter ⊓
      InternalParameterizedCanonicalResultFold.sourcePremises
        (finalData p) input typ parameter).imp
      ((InternalParameterizedCanonicalResultFold.foldGraph (finalData p)
        out input parameter).iff
        (graph2 (canonical p.base p.window) out input parameter))))

/-- Genuine SAME-final canonical-body closure. Parent canonicality is the
ACTUAL T fixedness used by the original typed checker. Body validity, actual
codomain and T fixedness are CONCLUSIONS at that identical final Data and
the actual single extended-Gamma parameter. No body C/Acc/fixedness, native
calibration, typed decoding or earlier-Data body theorem is a premise. -/
def FinalBodyFixedLaw (p : GlobalSourcePackage.Inputs) : Prop :=
  ∀ (positive : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (input d e body parameter bodyParameter : OTerm alpha),
  let after := finalData p
  Nonempty (Derivation positive Delta
    ((OriginalFunctionNeutrality.windowGraph (finalInputs p).window input parameter ⊓
      (OriginalLambdaTraversalInternal.LambdaFields input d e body parameter bodyParameter ⊓
        (graph2 (InternalOriginalUniformDescentSelection.validity after)
          InternalOriginalStepGuard.one input parameter ⊓
          InternalParameterizedBoundedDescentNormalizer.transitionGraph
            after.oldRepresentative (InternalOriginalUniformDescentSelection.validity after)
            input input parameter))).imp
      (graph2 (InternalOriginalUniformDescentSelection.validity after)
        InternalOriginalStepGuard.one body bodyParameter ⊓
        (graph1 InternalUnpair.left e body ⊓
          InternalParameterizedBoundedDescentNormalizer.transitionGraph
            after.oldRepresentative (InternalOriginalUniformDescentSelection.validity after)
            body body bodyParameter))))

/-- Exact lambda constructor equation at the ACTUAL final full canonical
fold, with an actual child graph of that SAME fold at actual childGamma.
No earlier fold, body canonicality or successful-run premise is substituted. -/
def FinalLambdaEquation (p : GlobalSourcePackage.Inputs) : Prop :=
  ∀ (positive : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (input d e body bodyOut out parameter bodyParameter : OTerm alpha),
  let after := finalData p
  Nonempty (Derivation positive Delta
    ((OriginalFunctionNeutrality.windowGraph (finalInputs p).window input parameter ⊓
      (OriginalLambdaTraversalInternal.LambdaFields input d e body parameter bodyParameter ⊓
        (graph2 (InternalOriginalUniformDescentSelection.validity after)
          InternalOriginalStepGuard.one input parameter ⊓
          InternalParameterizedCanonicalResultFold.foldGraph after bodyOut body bodyParameter))).imp
      ((InternalParameterizedCanonicalResultFold.foldGraph after out input parameter).iff
        (graph3 OriginalLambdaConstructor.constructor out d e bodyOut))))

/-- All-input preservation of all four original raw leaves, including
malformed/rejected vectors, plus complete native calibration of preparation
and of the ACTUAL final input tuple. No internal law follows by reflection. -/
def NativePreparation (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) : Prop :=
  GlobalSourcePackage.InputsCalibrated n arity (prepareInputs p) ∧
    GlobalSourcePackage.InputsCalibrated n arity (finalInputs p) ∧
    (∀ v : List.Vector Nat 2,
      evaluate (prepareInputs p).base.oldSource v = evaluate p.base.oldSource v ∧
      evaluate (prepareInputs p).base.oldTarget v = evaluate p.base.oldTarget v ∧
      evaluate (prepareInputs p).base.oldRepresentative v = evaluate p.base.oldRepresentative v ∧
      evaluate (prepareInputs p).base.member v = evaluate p.base.member v)

/-- The WHOLE hereditary/global retained package coexists with independent
transparent validity and canonical/body laws at one actual final tuple.
This does not assert lambda/substitution computability or closed ID1. -/
def Properties (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) : Prop :=
  NativePreparation n arity p ∧
    OriginalHereditaryLambdaGlobal.Properties n arity (prepareInputs p) ∧
    OriginalTransparentLambdaFinal.InternalLaws p.base (finalData p) ∧
    FinalTransitionLaw p ∧ FinalCanonicalLaw p ∧ FinalBodyFixedLaw p ∧ FinalLambdaEquation p

/- FROZEN PLAN, NOT AN ACCEPTANCE CLAIM.

The leaf AST is finite and acyclic: transparentData, leafData and leaf never
refer to preparedData, canonical's own output or finalInputs. The active
native proof must use ORIGINAL application/lambda representative factorization
and actual decoded child Gamma, while the inactive branch is literal oldR.

Internal child source acceptance at the same final validator remains a
separate required supplier, provided by the transparent final-validity lane;
it must be proved, not added to these final targets. Window validity transfers
because childParameter preserves the SAME outer context. C's output laws,
idempotence and original-observer laws must then pay guard redundancy and
collapse the outer application sidecar to C. Only then may the independent
SAME-final transition/canonical equivalences be proved. The lambda recurrence
and original constructor injectivity yield child C fixedness; the final
transition equivalence transports it to SAME-final T fixedness. Existing
final canonical consumers supply parent T fixedness for canonical outputs.

None of these later obligations follows from generic traversal calibration,
native finite-class mathematics, an earlierData one-level lambda equation,
or a supplied body-computability/accessibility hypothesis.
-/

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalSelection
