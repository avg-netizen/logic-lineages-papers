module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalApplicationStepDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTypedEdgePresentationDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeFoldCalibrationDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldClosureDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCertifiedSourceGuardSelection
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Only original finite Program leaves. Every constructed checker and
representative below shares these SAME leaves. There is no correctness,
congruence, lift, totality or derivability field. -/
structure Data where
  oldValidity : InternalOriginalStepGuard.Data
  member : Program 1
  oldEdge : InternalQuotientEdgeChecker.Data
  oldTyped : Program 2

/-- The exact previously selected original application-step leaves. -/
def baseData (data : Data) : InternalOriginalApplicationStep.Data where
  oldValidity := data.oldValidity
  member := data.member
  oldStep := data.oldEdge.stepProgram

/-- V is literally recursiveData on the shared original validity/member
leaves. Its target remains the original packed validity, without a universe
filter. Only the later selected STEP adds source validity of its raw target. -/
def validity (data : Data) : InternalOriginalStepGuard.Data :=
  InternalApplicationValidityStack.recursiveData data.oldValidity data.member

def endpoint (data : Data) : Program 5 :=
  InternalOriginalApplicationStep.endpoint (baseData data)

/-- The already constructed outer-guarded normalized original checker,
including the SAME recursive endpoint and unchanged old step leaf. -/
def baseStep (data : Data) : Program 3 :=
  InternalOriginalApplicationStep.stepChecker (baseData data)

/-- The exact checked representative normalizer N, not a new representative
selected independently for the typed checker or either endpoint. -/
def normalizer (data : Data) : Program 1 :=
  InternalRepresentativeFoldCalibration.normalizer data.oldValidity data.member data.oldEdge

/-- H uses the SAME root guard, leaf and combine as N and its unchanged
2*original-payload+1 run. Its graph is not replaced internally by constant one. -/
def goodRun (data : Data) : Program 1 :=
  InternalApplicationCertifiedResultFoldClosure.goodRun
    (InternalRepresentativeFoldCalibration.rootGuard data.oldValidity data.member)
    (InternalRepresentativeFoldCalibration.leaf data.oldValidity data.member data.oldEdge)
    (InternalRepresentativeFoldCalibration.combine data.oldEdge)

def unaryAt {m : Nat} (program : Program 1) (coordinate : Fin m) : Program m :=
  .composition program (fun _ : Fin 1 => .projection coordinate)

/-- Exact-one conjunction on [rawSource,rawTarget,rawStep]: the original
guarded application step, source-universe validity of rawTarget, and the
actual successful N-run checks at BOTH raw endpoints. -/
def stepChecker (data : Data) : Program 3 :=
  InternalAcceptance.conjunction (baseStep data)
    (InternalAcceptance.conjunction (unaryAt (validity data).sourceValid 1)
      (InternalAcceptance.conjunction (unaryAt (goodRun data) 0)
        (unaryAt (goodRun data) 1)))

/-- Both representative fields are literally withRepresentatives V FoldedData.
The source uses V.sourceValid and the target uses V.targetValid. -/
def representatives (data : Data) : InternalQuotientEdgeChecker.Data :=
  InternalRepresentativeTag.withRepresentatives (validity data)
    (InternalRepresentativeFoldCalibration.foldedData
      data.oldValidity data.member data.oldEdge)

/-- Replace ONLY the step field by the strengthened shared checker. No
target-universe filter is inserted into the target representative. -/
def edgeData (data : Data) : InternalQuotientEdgeChecker.Data :=
  { representatives data with stepProgram := stepChecker data }

/-- The existing canonical [value,type] checker, including its shared
source validity, raw outer-type equality and membership guard. -/
def baseTyped (data : Data) : Program 2 :=
  InternalTypedEdgePresentation.typedChecker (validity data) data.member data.oldTyped

/-- An actual equality-test AST comparing N(value) with the same raw value,
not a semantic canonicality or an assumed internal fixed-point law. -/
def fixedPoint (data : Data) : Program 2 :=
  InternalApplicationStepPeel.same (unaryAt (normalizer data) 0) (.projection 0)

/-- Exact-one conjunction on [value,type]. The literal old canonical typed
wrapper remains; actual good-run acceptance and N(value)=value are explicit. -/
def typedChecker (data : Data) : Program 2 :=
  InternalAcceptance.conjunction (baseTyped data)
    (InternalAcceptance.conjunction (unaryAt (goodRun data) 0) (fixedPoint data))

/-- External calibration of all shared original leaves on EVERY natural
input. It gives no internal inference rule on symbolic terms. -/
def Calibrated (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool) (data : Data) : Prop :=
  InternalOriginalStepGuard.Calibrated n arity symbols S Gamma data.oldValidity ∧
    (InternalStructuralEndpointGuard.MembershipCalibrated S data.member ∧
      (InternalQuotientEdgeChecker.Calibrated n arity symbols S Gamma table data.oldEdge ∧
        InternalOriginalTypedCarrier.Calibrated n arity symbols S Gamma data.oldTyped))

/-- All constructed functions keep their unchanged original all-input
semantics. The first conjunct includes V, endpoint and baseStep; edgeData
includes the strengthened step and BOTH selected representatives. -/
def SelectedCalibrated (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool) (data : Data) : Prop :=
  InternalOriginalApplicationStep.SelectedCalibrated n arity symbols S Gamma table (baseData data) ∧
    (InternalQuotientEdgeChecker.Calibrated n arity symbols S Gamma table (edgeData data) ∧
      (InternalOriginalTypedCarrier.Calibrated n arity symbols S Gamma (typedChecker data) ∧
        ∀ v : List.Vector Nat 3,
          evaluate (InternalQuotientEdgeChecker.checker (edgeData data)) v =
            (NumberedNumericQuotientEdge.numericEdgeTest n arity symbols S Gamma table
              (v.get 0) (v.get 1) (v.get 2)).toNat))

def stepAccepted {α : Type} (data : Data) (s t k : OTerm α) : Formula α :=
  graph3 (stepChecker data) InternalOriginalStepGuard.one s t k

/-- Internal factorization exposes actual selected Program graphs. The
source validity of t is a new explicit STEP guard, not global target validity. -/
def stepFactors {α : Type} (data : Data) (s t k : OTerm α) : Formula α :=
  graph3 (baseStep data) InternalOriginalStepGuard.one s t k ⊓
    (graph1 (validity data).sourceValid InternalOriginalStepGuard.one t ⊓
      (graph1 (goodRun data) InternalOriginalStepGuard.one s ⊓
        graph1 (goodRun data) InternalOriginalStepGuard.one t))

def typedAccepted {α : Type} (data : Data) (value typ : OTerm α) : Formula α :=
  graph2 (typedChecker data) InternalOriginalStepGuard.one value typ

/-- Fixed-point acceptance is the actual N graph with output value at input
value. Neither H=1 nor N(value)=value is inferred by semantic reflection. -/
def typedFactors {α : Type} (data : Data) (value typ : OTerm α) : Formula α :=
  graph2 (baseTyped data) InternalOriginalStepGuard.one value typ ⊓
    (graph1 (goodRun data) InternalOriginalStepGuard.one value ⊓
      graph1 (normalizer data) value value)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCertifiedSourceGuardSelection
