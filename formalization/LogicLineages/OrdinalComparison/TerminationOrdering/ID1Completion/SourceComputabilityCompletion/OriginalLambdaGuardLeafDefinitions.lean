module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorLeafDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaCertificateDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaGuardLeaf
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Literal lambda-tag test on the ORIGINAL raw packed input. This total test
alone does not assert that a malformed input is a typed lambda. -/
def lambdaTest : Program 1 :=
  InternalApplicationStepPeel.same OriginalLambdaConstructor.tag
    (InternalLessThan.constantOne 1)

def sourceLambda : Program 4 :=
  .composition lambdaTest (fun _ : Fin 1 => .projection 0)

def targetLambda : Program 4 :=
  .composition lambdaTest (fun _ : Fin 1 => .projection 1)

/-- The raw target is the literal same-type bottom of the raw source. The
existing constructor retains both original occurrences of the outer type. -/
def sameBottom : Program 4 :=
  InternalApplicationStepPeel.same (.projection 1) OriginalConstructorLeaf.expectedBottom

/-- Actual lambda domain and outer-arrow codomain selectors. The codomain
uses the original successor-of-pair type numbering, not an Encodable Gamma. -/
def sourceDomain : Program 4 :=
  .composition OriginalLambdaConstructor.domain (fun _ : Fin 1 => .projection 0)

def sourceCodomain : Program 4 :=
  .composition InternalListCodec.tailCode
    (fun _ : Fin 1 => leftOf (.projection 0))

def sourceBody : Program 4 :=
  .composition OriginalLambdaConstructor.bodyCode ![sourceCodomain,.projection 0]

def targetBody : Program 4 :=
  .composition OriginalLambdaConstructor.bodyCode ![sourceCodomain,.projection 1]

/-- Explicit PR counterpart of OriginalLambdaCertificate.stripStep. Only one
original position-list entry is removed. The replacement/root pair is copied
unchanged, including on malformed inputs. -/
def stripCertificate : Program 1 :=
  pairOf
    (.composition InternalListCodec.tailCode (fun _ : Fin 1 => InternalUnpair.left))
    InternalUnpair.right

def childCertificate : Program 4 :=
  .composition stripCertificate (fun _ : Fin 1 => .projection 2)

/-- Retain the ORIGINAL outer context code and cons the ACTUAL source lambda
domain onto the ORIGINAL encoded Gamma. No typesNumber Gamma is substituted. -/
def childParameter : Program 4 :=
  pairOf (leftOf (.projection 3))
    (consOf sourceDomain (rightOf (.projection 3)))

/-- The unchanged old leaf is invoked on the actual original body payloads,
with the stripped SAME certificate and the single extended runtime parameter. -/
def childCheck (oldStep : Program 4) : Program 4 :=
  .composition oldStep ![sourceBody,targetBody,childCertificate,childParameter]

/-- Both lambda tags, domains and outer types are literal original fields.
The source tag is the guard trigger; these are the demanded target fields. -/
def matchingTarget : Program 4 :=
  InternalAcceptance.conjunction targetLambda
    (InternalAcceptance.conjunction
      (InternalApplicationStepPeel.same
        (leftOf (.projection 1)) (leftOf (.projection 0)))
      (InternalApplicationStepPeel.same
        (.composition OriginalLambdaConstructor.domain (fun _ : Fin 1 => .projection 1))
        sourceDomain))

def childGuard (oldStep : Program 4) : Program 4 :=
  InternalAcceptance.conjunction matchingTarget (childCheck oldStep)

/-- Demand a matching accepted child only in the literal-lambda/nonbottom
case. Every other case takes the accepting branch. Normalization fixes the
behavior for arbitrary symbolic control values, not only Boolean evaluations. -/
def guard (oldStep : Program 4) : Program 4 :=
  InternalAcceptance.branch
    (LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalization.normalize sourceLambda)
    (InternalLessThan.constantOne 4)
    (InternalAcceptance.branch
      (LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalization.normalize sameBottom)
      (childGuard oldStep) (InternalLessThan.constantOne 4))

/-- Preserve the WHOLE original leaf as a literal factor. The original raw
source, target, supplied certificate and parameter remain its four inputs. -/
def refined (oldStep : Program 4) : Program 4 :=
  InternalAcceptance.conjunction oldStep (guard oldStep)

abbrev accepted {alpha : Type} (p : Program 4)
    (source target certificate parameter : OTerm alpha) : Formula alpha :=
  OriginalConstructorLeaf.accepted p source target certificate parameter

abbrev guardAccepted {alpha : Type} (oldStep : Program 4)
    (source target certificate parameter : OTerm alpha) : Formula alpha :=
  accepted (guard oldStep) source target certificate parameter

/-- Original-calculus antecedent only. No native parse, typing, calibration,
window membership or source-relation oracle is an internal premise. -/
def LambdaNonbottom {alpha : Type}
    (source target certificate parameter : OTerm alpha) : Formula alpha :=
  accepted sourceLambda source target certificate parameter ⊓
    graph4 sameBottom (SourceComputabilityFormulaSupportProof.numeral 0)
      source target certificate parameter

def LeafHasGuard (oldStep leaf : Program 4) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (source target certificate parameter : OTerm alpha),
  Nonempty (Derivation body Delta
    ((accepted leaf source target certificate parameter).imp
      (guardAccepted oldStep source target certificate parameter)))

/-- The concrete guard's internal nonbottom branch exposes both the original
matching-target test and the composition that calls oldStep on the child. -/
def LeafHasChildBranch (oldStep leaf : Program 4) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (source target certificate parameter : OTerm alpha),
  Nonempty (Derivation body Delta
    ((accepted leaf source target certificate parameter ⊓
      LambdaNonbottom source target certificate parameter).imp
        (accepted matchingTarget source target certificate parameter ⊓
          accepted (childCheck oldStep) source target certificate parameter)))

/-- Connected child witnesses, all generated from the same four original
inputs. The final conjunct is the ORIGINAL old leaf graph at those witnesses,
not merely acceptance of a replacement relation or an evaluated Boolean. -/
def ChildRecovered {alpha : Type} (oldStep : Program 4)
    (source target certificate parameter sourceChild targetChild childStep childParam : OTerm alpha) :
    Formula alpha :=
  accepted matchingTarget source target certificate parameter ⊓
    (graph4 sourceBody sourceChild source target certificate parameter ⊓
      (graph4 targetBody targetChild source target certificate parameter ⊓
        (graph4 childCertificate childStep source target certificate parameter ⊓
          (graph4 childParameter childParam source target certificate parameter ⊓
            accepted oldStep sourceChild targetChild childStep childParam))))

/-- Eliminate child witnesses INTERNALLY using original Program totality and
composition. The caller supplies no selector witnesses. This is independent
of native calibration; its continuation receives the actual old-leaf graph. -/
def InternalChildElimination (oldStep leaf : Program 4) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (source target certificate parameter : OTerm alpha) (psi : Formula alpha),
  Nonempty (Derivation body Delta
    (accepted leaf source target certificate parameter ⊓
      LambdaNonbottom source target certificate parameter)) →
  (∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)),
    (∀ h ∈ Delta, h.relabel j ∈ Theta) →
    ∀ sourceChild targetChild childStep childParam : OTerm beta,
    Nonempty (Derivation body Theta
      (ChildRecovered oldStep (source.relabel j) (target.relabel j)
        (certificate.relabel j) (parameter.relabel j)
        sourceChild targetChild childStep childParam)) →
    Nonempty (Derivation body Theta (psi.relabel j))) →
  Nonempty (Derivation body Delta psi)

/-- Only the oldStep AST changes. A later global theorem must separately
retain the entire current Package and neutral/variable laws at ONE final tuple;
all-input evaluation equality alone is not that internal theorem. -/
def refineInputs (p : GlobalSourcePackage.Inputs) : GlobalSourcePackage.Inputs :=
  { p with oldStep := refined p.oldStep }

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaGuardLeaf
