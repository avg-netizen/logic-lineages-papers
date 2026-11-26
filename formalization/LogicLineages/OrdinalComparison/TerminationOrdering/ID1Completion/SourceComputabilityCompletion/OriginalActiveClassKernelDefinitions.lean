module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveObservedMinimumDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveClassKernel
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors (graph2)
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Target acceptance and original window/source activation are separate
literal guards. No minimum or newly selected representative occurs here. -/
def domainProgram (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) : Program 2 :=
  InternalAcceptance.conjunction (OriginalTypedDecoder.target H G)
    (OriginalActiveObservedClass.activation p H G W)

/-- Equality of two outputs of the ORIGINAL pre-minimum representative key.
Inputs remain [seed,candidate,parameter], with one shared runtime parameter. -/
def keyTest (R : Program 2) : Program 3 :=
  InternalApplicationStepPeel.same
    (.composition R ![.projection 0,.projection 2])
    (.composition R ![.projection 1,.projection 2])

/-- The literal observer equality already used by the accepted observed
class wrapper; the candidate query precedes the seed query. -/
def observerTest (O : Program 1) : Program 3 :=
  InternalApplicationStepPeel.same
    (.composition O (fun _ : Fin 1 => .projection 1))
    (.composition O (fun _ : Fin 1 => .projection 0))

/-- On an active original seed, require an original active typed candidate
and equality of the original representative keys. The key is p's supplied
oldRepresentative, before any minimum construction, so this AST is acyclic. -/
def kernel (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) : Program 3 :=
  InternalAcceptance.conjunction
    (.composition (domainProgram p H G W) ![.projection 1,.projection 2])
    (keyTest p.base.oldRepresentative)

/-- Preserve the COMPLETE old class test on every inactive seed, including
malformed inputs and nonclosed windows. All-vector equality with the original
classValue is a separate native obligation, not an internal inference rule. -/
def classTest (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) : Program 3 :=
  InternalAcceptance.branch
    (.composition (OriginalActiveObservedClass.activation p H G W)
      ![.projection 0,.projection 2])
    P (kernel p H G W)

/-- Exactly the existing observer guard and reflexive wrapper applied to the
new all-vector-calibrated class implementation. No new minimum is used. -/
def relationTest (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (O : Program 1) (P : Program 3) : Program 3 :=
  OriginalTransparentMinimum.reflexiveClassTest (OriginalTypedDecoder.target H G)
    (OriginalActiveObservedClass.classTest p H G W O (classTest p H G W P))

def Domain {alpha : Type} (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (seed parameter : OTerm alpha) : Formula alpha :=
  graph2 (OriginalTypedDecoder.target H G) InternalOriginalStepGuard.one seed parameter ⊓
    graph2 (OriginalActiveObservedClass.activation p H G W)
      InternalOriginalStepGuard.one seed parameter

def Accepted {alpha : Type} (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (O : Program 1) (P : Program 3)
    (seed candidate parameter : OTerm alpha) : Formula alpha :=
  OriginalTransparentMinimum.graph3 (relationTest p H G W O P)
    InternalOriginalStepGuard.one seed candidate parameter

/-- Independent internal characterization of the actual wrapped relation.
Every key/observer equality is an actual Program graph; no semantic class
membership, native calibration or structural-coherence premise is supplied. -/
def CharacterizationLaw (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (O : Program 1) (P : Program 3) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (seed candidate parameter : OTerm alpha),
  Nonempty (Derivation body Delta
    ((Domain p H G W seed parameter).imp
      ((Accepted p H G W O P seed candidate parameter).iff
        (Domain p H G W candidate parameter ⊓
          (OriginalTransparentMinimum.graph3 (keyTest p.base.oldRepresentative)
            InternalOriginalStepGuard.one seed candidate parameter ⊓
            OriginalTransparentMinimum.graph3 (observerTest O)
              InternalOriginalStepGuard.one seed candidate parameter)))))

/-- An actual hit from an original active typed seed pays the candidate's
original target, source and window guards internally. -/
def HitDomainLaw (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (O : Program 1) (P : Program 3) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (seed candidate parameter : OTerm alpha),
  Nonempty (Derivation body Delta
    ((Domain p H G W seed parameter ⊓
      Accepted p H G W O P seed candidate parameter).imp
      (Domain p H G W candidate parameter)))

/-- Actual related seeds have identical wrapped acceptance rows at every
probe and the SAME parameter. The original key and observer are arbitrary
Programs; their totality/functionality must establish this derivation. -/
def RowCoherenceLaw (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (O : Program 1) (P : Program 3) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (seed other probe parameter : OTerm alpha),
  Nonempty (Derivation body Delta
    ((Domain p H G W seed parameter ⊓
      Accepted p H G W O P seed other parameter).imp
      ((Accepted p H G W O P seed probe parameter).iff
        (Accepted p H G W O P other probe parameter))))

/- The independent internal laws concern this explicit implementation.
Its correspondence to the original classValue must be proved on EVERY vector
before adoption. Canonical cancellation, class transport through substitution
or erasure, internal I/C and closed accessibility are separate obligations. -/
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveClassKernel
