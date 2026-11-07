module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GammaGuardedSourceDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GammaGuardedSourceTargets
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition
open SourceComputabilityFormulaSupportProof GammaGuardedSource
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- ALL natural inputs, including malformed object and context codes. -/
def ActualBaseCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat)
    (oldSource : SourcePresentation.Data) (oldComp : JointGammaComputability.Data)
    (valid gamma : Program 1),
  ContextUniform.Calibrated oldSource n arity →
  JointGammaComputability.Calibrated oldComp n arity →
  (∀ v, evaluate valid v = JointGammaDomain.guardValue (List.Vector.ofFn ![v.get 0,v.get 0])) →
  (∀ v, evaluate gamma v = ((Encodable.decode (v.get 0) : Option ContextUniform.Object).map
    (fun q => Encodable.encode q.1)).getD 0) →
  ContextUniform.Calibrated (baseSource oldSource gamma) n arity ∧
  JointGammaComputability.Calibrated (baseComputability oldComp valid gamma) n arity

/-- A genuine original-calculus supplier with arbitrary Programs and context.
There is NO closed-window premise and NO semantic reflection of open terms. -/
def ActualOriginalGuardTransport : Prop :=
  ∀ (oldSource : SourcePresentation.Data) (oldComp : JointGammaComputability.Data)
    (valid gamma : Program 1) (tag : Program 2) (window : Program 1)
    (context : Nat) (α : Type) (typ x y u : OrdinaryArithmetic.Term α),
  let src := source oldSource oldComp.typed valid gamma tag window
  let comp := computability oldComp valid gamma tag
  Nonempty (Derivation (SourcePresentation.sourceBody src context) []
    (((GuardedSource.literalTyped comp context typ x ⊓ GuardedSource.literalR src context x y) ⊓
      literalGuard comp y u).imp (literalGuard comp x u)))

/-- ONE calibrated source and computability witness precede every window and
open term. Their typed and ground closure remains available on subtype-closed
windows; SAME-Gamma argument-domain transport is unconditional on context. -/
def ActualUniformGuardClosureExists : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
  ∃ (src : SourcePresentation.Data) (comp : JointGammaComputability.Data),
  ContextUniform.Calibrated src n arity ∧
  JointGammaComputability.Calibrated comp n arity ∧
  (∀ (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool),
    SubtypeClosed (fun tau => tau ∈ S) →
    ∀ (α : Type),
    let context := OrdinaryArithmeticQuotient.contextCode symbols S table
    (∀ (typ x y : OrdinaryArithmetic.Term α),
      Nonempty (Derivation (SourcePresentation.sourceBody src context) []
        ((GuardedSource.literalTyped comp context typ x ⊓ GuardedSource.literalR src context x y).imp
          (GuardedSource.literalTyped comp context typ y)))) ∧
    (∀ (x y : OrdinaryArithmetic.Term α),
      Nonempty (Derivation (SourcePresentation.sourceBody src context) []
        ((GuardedSource.literalComputable comp context .ground x ⊓ GuardedSource.literalR src context x y).imp
          (GuardedSource.literalComputable comp context .ground y))))) ∧
  (∀ (context : Nat) (α : Type) (typ x y u : OrdinaryArithmetic.Term α),
    Nonempty (Derivation (SourcePresentation.sourceBody src context) []
      (((GuardedSource.literalTyped comp context typ x ⊓ GuardedSource.literalR src context x y) ⊓
        literalGuard comp y u).imp (literalGuard comp x u))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GammaGuardedSourceTargets
