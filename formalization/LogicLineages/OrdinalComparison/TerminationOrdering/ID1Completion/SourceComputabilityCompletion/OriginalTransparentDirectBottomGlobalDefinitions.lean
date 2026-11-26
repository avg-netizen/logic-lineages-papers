module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepGlobalTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomGlobal
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Make the original source concrete BEFORE either step refinement. No
variable refinement is inserted here; the retained lambda pipeline supplies
its one final variable refinement later. -/
def concreteInputs (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) :=
  OriginalTransparentDecoderSelection.transparentInputs H G W p

def source (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) : Program 2 :=
  OriginalUniverseDecoder.source H G (InternalOriginalUniformContextMembership.contextMember p.base.member) W

/-- Both direct-bottom and the later lambda normalizer capture this SAME
concrete original source, never the later final validator. -/
def initial (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) :=
  OriginalTransparentDirectBottom.refineInputs (concreteInputs p H G W)

def finalInputs (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) :=
  OriginalTransparentLambdaStepGlobal.finalInputs (initial p H G W) H G W P

def NativePreparation (n : Nat) (arity : Fin n → Nat) (p : GlobalSourcePackage.Inputs)
    (H G : Program 1) (W : Program 2) (P : Program 3) : Prop :=
  GlobalSourcePackage.InputsCalibrated n arity (concreteInputs p H G W) ∧
    GlobalSourcePackage.InputsCalibrated n arity (initial p H G W) ∧
    GlobalSourcePackage.InputsCalibrated n arity (finalInputs p H G W P) ∧
    (∀ v : List.Vector Nat 4,
      evaluate (initial p H G W).oldStep v = evaluate p.oldStep v ∧
      evaluate (finalInputs p H G W P).oldStep v = evaluate p.oldStep v)

/-- Direct bottom at the SAME actual final leaf whose complete lambda
introduction/retention package is retained below. Source is the concrete
original decoder explicitly, not inferred from any final child graph. -/
def FinalIntroduction (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (s t cert parameter typ : OTerm alpha),
  Nonempty (Derivation body Delta
    ((OriginalTransparentDirectBottom.Premises (source p H G W) s t cert parameter typ).imp
      (graph4 (finalInputs p H G W P).oldStep InternalOriginalStepGuard.one s t cert parameter)))

def Properties (n : Nat) (arity : Fin n → Nat) (p : GlobalSourcePackage.Inputs)
    (H G : Program 1) (W : Program 2) (P : Program 3) : Prop :=
  OriginalTransparentDecoderSelection.Calibration n arity p H G W ∧
    NativePreparation n arity p H G W P ∧
    OriginalTransparentLambdaStepGlobal.Properties n arity (initial p H G W) H G W P ∧
    FinalIntroduction p H G W P

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomGlobal
