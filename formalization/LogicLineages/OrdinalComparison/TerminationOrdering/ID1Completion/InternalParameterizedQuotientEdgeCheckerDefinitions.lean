module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformStepGuardDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalResultFoldDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientEdgeTypeGuardDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedQuotientEdgeChecker
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open InternalOriginalUniformDescentSelection (Data validity selectedTyped)
open InternalParameterizedCanonicalResultFold (foldN)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The original source-universe filter selects N exactly at output one.
The source representative is zero on every other source-validity output. -/
def sourceRepresentative (data : Data) : Program 2 :=
  InternalAcceptance.branch
    (InternalApplicationValidityStack.exactOne (validity data))
    (InternalAcceptance.constantZero 2) (foldN data)

/-- The target remains N on every packed input, including inputs outside
the source universe. No source-validity filter is added to this program. -/
def targetRepresentative (data : Data) : Program 2 :=
  foldN data

/-- All outer nodes read [source endpoint,target endpoint,certificate,p].
The unchanged original unary selectors read only the certificate field. -/
def field (selector : Program 1) : Program 4 :=
  .composition selector (fun _ : Fin 1 => .projection 2)

def stepAt (data : Data) (oldStep : Program 4) : Program 4 :=
  .composition (InternalOriginalUniformStepGuard.stepChecker data oldStep)
    ![field source,field target,field step,.projection 3]

def representativeAt (representative : Program 2) (selector : Program 1) : Program 4 :=
  .composition representative ![field selector,.projection 3]

def representativeCheck (representative : Program 2) (selector : Program 1)
    (endpoint : Fin 4) : Program 4 :=
  .composition InternalEqualityTest.equalityTest
    ![representativeAt representative selector,.projection endpoint]

/-- The original three quotient-edge factors at one unchanged parameter:
actual W, source representative equality and target representative equality. -/
def coreChecker (data : Data) (oldStep : Program 4) : Program 4 :=
  InternalAcceptance.conjunction (stepAt data oldStep)
    (InternalAcceptance.conjunction
      (representativeCheck (sourceRepresentative data) source 0)
      (representativeCheck (targetRepresentative data) target 1))

/-- The wrapper uses the actual source endpoint's original outer type. -/
def sourceType : Program 4 :=
  leftOf (.projection 0)

def typedAt (data : Data) (endpoint : Fin 4) : Program 4 :=
  .composition (selectedTyped data) ![.projection endpoint,sourceType,.projection 3]

/-- Both selected typed predicates inspect the same source type and the
same p. Their redundancy for original accepted edges is proved separately. -/
def checker (data : Data) (oldStep : Program 4) : Program 4 :=
  InternalAcceptance.conjunction (coreChecker data oldStep)
    (InternalAcceptance.conjunction (typedAt data 0) (typedAt data 1))

def coreAccepted {α : Type} (data : Data) (oldStep : Program 4)
    (x y certificate parameter : OrdinaryArithmetic.Term α) : Formula α :=
  graph4 (coreChecker data oldStep) InternalOriginalStepGuard.one x y certificate parameter

def accepted {α : Type} (data : Data) (oldStep : Program 4)
    (x y certificate parameter : OrdinaryArithmetic.Term α) : Formula α :=
  graph4 (checker data oldStep) InternalOriginalStepGuard.one x y certificate parameter

def typedAccepted {α : Type} (data : Data)
    (value typ parameter : OrdinaryArithmetic.Term α) : Formula α :=
  graph3 (selectedTyped data) InternalOriginalStepGuard.one value typ parameter

def sourceRepresentativeGraph {α : Type} (data : Data)
    (out input parameter : OrdinaryArithmetic.Term α) : Formula α :=
  graph2 (sourceRepresentative data) out input parameter

def targetRepresentativeGraph {α : Type} (data : Data)
    (out input parameter : OrdinaryArithmetic.Term α) : Formula α :=
  graph2 (targetRepresentative data) out input parameter

def requirements {α : Type} (data : Data) (oldStep : Program 4)
    (x y rawSource rawTarget rawStep parameter : OrdinaryArithmetic.Term α) : Formula α :=
  InternalOriginalUniformStepGuard.stepAccepted data oldStep rawSource rawTarget rawStep parameter ⊓
    (sourceRepresentativeGraph data x rawSource parameter ⊓
      targetRepresentativeGraph data y rawTarget parameter)

/-- W itself supplies source validity. Thus its accepted source comparison
can expose the actual N graph without inserting a validity premise. -/
def normalizedRequirements {α : Type} (data : Data) (oldStep : Program 4)
    (x y rawSource rawTarget rawStep parameter : OrdinaryArithmetic.Term α) : Formula α :=
  InternalOriginalUniformStepGuard.stepAccepted data oldStep rawSource rawTarget rawStep parameter ⊓
    (InternalParameterizedCanonicalResultFold.foldGraph data x rawSource parameter ⊓
      InternalParameterizedCanonicalResultFold.foldGraph data y rawTarget parameter)

def sourceTypeGraph {α : Type} (typ x : OrdinaryArithmetic.Term α) : Formula α :=
  graph1 InternalUnpair.left typ x

def typedRequirements {α : Type} (data : Data) (oldStep : Program 4)
    (x y certificate typ parameter : OrdinaryArithmetic.Term α) : Formula α :=
  coreAccepted data oldStep x y certificate parameter ⊓
    (typedAccepted data x typ parameter ⊓ typedAccepted data y typ parameter)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedQuotientEdgeChecker
