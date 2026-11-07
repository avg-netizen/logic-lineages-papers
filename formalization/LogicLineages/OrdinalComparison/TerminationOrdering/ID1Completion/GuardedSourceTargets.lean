module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceTargets
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition
open InternalControlGraph GuardedSource SourceComputabilityFormulaSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- All-input equality to the ORIGINAL checker, including malformed contexts. -/
def ActualTypedRange : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (v : List.Vector Nat 3),
    JointGammaTyped.typedValue n arity v = 0 ∨ JointGammaTyped.typedValue n arity v = 1

/-- Calibration is an equality on EVERY input, not only typed/closed windows. -/
def ActualGuardedCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat)
    (oldSource : SourcePresentation.Data) (oldComp : JointGammaComputability.Data)
    (tag : Program 2) (window : Program 1),
  ContextUniform.Calibrated oldSource n arity →
  JointGammaComputability.Calibrated oldComp n arity →
  (∀ v, evaluate tag v = GuardCalibration.typeTagValue v) →
  (∀ v, evaluate window v = GuardCalibration.validWindowValue n v) →
  ContextUniform.Calibrated (source oldSource oldComp.typed tag window) n arity ∧
  JointGammaComputability.Calibrated (computability oldComp tag) n arity

/-- A generic graph supplier, not the final source package. Only a SINGLE
fixed numeral evaluation selects the branch. No symbolic semantic reflection. -/
def ActualOriginalGuardedCertificatePreservation : Prop :=
  ∀ (body : Positive (Fin 1)) (typed : Program 3) (positive : Program 4)
    (tag : Program 2) (window : Program 1) (context : Nat),
  evaluate window (List.Vector.ofFn ![context]) = 1 →
  ∀ (α : Type) (typ x y certificate : OTerm α),
  let one := OrdinaryArithmetic.succTerm OrdinaryArithmetic.zeroTerm
  Nonempty (Derivation body []
    ((programGraph (guardedTyped typed tag) one ![numeral context,typ,x] ⊓
      programGraph (guardedPositive positive typed tag window) one
        ![numeral context,x,y,certificate]).imp
      (programGraph (guardedTyped typed tag) one ![numeral context,typ,y])))

/-- Exact final typed R closure. Particular source/comp witnesses precede
ALL windows, tables and free terms. No strict-order assumption or closure
field is supplied. The source body, typed compiler and certificateGraph are
literally the original ones. -/
def ActualUniformTypedSuccessorExists : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
  ∃ (source : SourcePresentation.Data) (comp : JointGammaComputability.Data),
  ContextUniform.Calibrated source n arity ∧
  JointGammaComputability.Calibrated comp n arity ∧
  ∀ (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool),
  SubtypeClosed (fun tau => tau ∈ S) →
  ∀ (α : Type) (typ x y : OrdinaryArithmetic.Term α),
  let context := OrdinaryArithmeticQuotient.contextCode symbols S table
  Nonempty (Derivation (SourcePresentation.sourceBody source context) []
    ((literalTyped comp context typ x ⊓ literalR source context x y).imp
      (literalTyped comp context typ y)))

/-- Stronger final gate: the SAME witnesses also prove exact ground C_tau
downward closure through literal source R, without changing sourceBody or C. -/
def ActualUniformGroundClosureExists : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
  ∃ (source : SourcePresentation.Data) (comp : JointGammaComputability.Data),
  ContextUniform.Calibrated source n arity ∧
  JointGammaComputability.Calibrated comp n arity ∧
  ∀ (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool),
  SubtypeClosed (fun tau => tau ∈ S) →
  ∀ (α : Type),
  let context := OrdinaryArithmeticQuotient.contextCode symbols S table
  (∀ (typ x y : OrdinaryArithmetic.Term α),
    Nonempty (Derivation (SourcePresentation.sourceBody source context) []
      ((literalTyped comp context typ x ⊓ literalR source context x y).imp
        (literalTyped comp context typ y)))) ∧
  (∀ (x y : OrdinaryArithmetic.Term α),
    Nonempty (Derivation (SourcePresentation.sourceBody source context) []
      ((literalComputable comp context .ground x ⊓ literalR source context x y).imp
        (literalComputable comp context .ground y))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceTargets
