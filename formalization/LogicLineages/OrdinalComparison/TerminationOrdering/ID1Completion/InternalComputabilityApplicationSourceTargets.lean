module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityApplicationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationGuardedTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityApplicationSourceTargets
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition
open SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative
open InternalComputabilityApplication
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- One calibrated original source/computability pair and one actual result
builder precede every source window and ambient context. The internal typed,
ground, guard, totality and uniqueness suppliers are retained for this SAME
pair. The two final clauses are the application case of computability, with
activation and arithmetic metadata discharged rather than assumed. -/
def ActualUniformSourceComputableApplication : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
  ∃ (src : SourcePresentation.Data) (comp : JointGammaComputability.Data) (result : Program 5),
  ContextUniform.Calibrated src n arity ∧
  JointGammaComputability.Calibrated comp n arity ∧
  (∀ v, evaluate result v = ApplicationResultBuilder.resultValue n arity v) ∧
  (∀ (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool),
    SubtypeClosed (fun tau => tau ∈ S) →
    ∀ (α : Type),
    let context := OrdinaryArithmeticQuotient.contextCode symbols S table
    (∀ (typ x y : OTerm α),
      Nonempty (Derivation (SourcePresentation.sourceBody src context) []
        ((GuardedSource.literalTyped comp context typ x ⊓ GuardedSource.literalR src context x y).imp
          (GuardedSource.literalTyped comp context typ y)))) ∧
    (∀ (x y : OTerm α),
      Nonempty (Derivation (SourcePresentation.sourceBody src context) []
        ((GuardedSource.literalComputable comp context .ground x ⊓ GuardedSource.literalR src context x y).imp
          (GuardedSource.literalComputable comp context .ground y)))) ∧
    (∀ (sigma tau : Ty) (f a : OTerm α),
      Nonempty (Derivation (SourcePresentation.sourceBody src context) []
        ((ApplicationGuarded.domain comp context sigma tau f a).imp
          (ApplicationGuarded.existsApplication comp context sigma tau f a)))) ∧
    (∀ (sigma tau : Ty) (f a out other : OTerm α),
      Nonempty (Derivation (SourcePresentation.sourceBody src context) []
        ((ApplicationGuarded.domain comp context sigma tau f a).imp
          ((InternalApplication.literalApplication comp.application context sigma tau f a out ⊓
            InternalApplication.literalApplication comp.application context sigma tau f a other).imp
            (InternalControlGraph.equal out other))))) ∧
    (∀ (sigma tau : Ty) (f a out : OTerm α),
      Nonempty (Derivation (SourcePresentation.sourceBody src context) []
        ((premises comp sigma tau (numeral context) f a).imp
          ((accepted comp sigma tau (numeral context) f a out).imp
            (computable comp tau (numeral context) out))))) ∧
    (∀ (sigma tau : Ty) (f a out : OTerm α),
      Nonempty (Derivation (SourcePresentation.sourceBody src context) []
        ((premises comp sigma tau (numeral context) f a).imp
          ((InternalControlGraph.programGraph result out (arguments (numeral context) sigma tau f a)).imp
            (computable comp tau (numeral context) out)))))) ∧
  (∀ (context : Nat) (α : Type) (typ x y u : OTerm α),
    Nonempty (Derivation (SourcePresentation.sourceBody src context) []
      (((GuardedSource.literalTyped comp context typ x ⊓ GuardedSource.literalR src context x y) ⊓
        GammaGuardedSource.literalGuard comp y u).imp (GammaGuardedSource.literalGuard comp x u))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityApplicationSourceTargets
