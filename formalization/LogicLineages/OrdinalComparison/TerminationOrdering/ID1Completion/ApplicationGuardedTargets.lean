module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationGuardedDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationGuardedTargets
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative ApplicationGuarded
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Only the two closed numeral facts are evaluated. Current typed/guard graphs
are recovered directly from the literal object-language premises. -/
def ActualOriginalActivation : Prop :=
  ∀ (body : Positive (Fin 1)) (comp : JointGammaComputability.Data)
    (window : Program 1) (arrow : Program 2) (context : Nat) (sigma tau : Ty),
  evaluate window (List.Vector.ofFn ![context]) = 1 →
  evaluate arrow (List.Vector.ofFn ![typeNumber sigma,typeNumber tau]) = typeNumber (.arrow sigma tau) →
  ∀ (α : Type) (f a : OTerm α),
  Nonempty (Derivation body [] ((domain comp context sigma tau f a).imp
    (programGraph (ApplicationDomain.activation window comp.typed comp.guard arrow)
      (OrdinaryArithmetic.succTerm OrdinaryArithmetic.zeroTerm)
      ![numeral context,numeral (typeNumber sigma),numeral (typeNumber tau),f,a])))

def ActualOriginalTotality : Prop :=
  ∀ (body : Positive (Fin 1)) (old : JointGammaComputability.Data)
    (window : Program 1) (arrow : Program 2) (result : Program 5)
    (context : Nat) (sigma tau : Ty),
  evaluate window (List.Vector.ofFn ![context]) = 1 →
  evaluate arrow (List.Vector.ofFn ![typeNumber sigma,typeNumber tau]) = typeNumber (.arrow sigma tau) →
  ∀ (α : Type) (f a : OTerm α),
  let comp := InternalApplication.computability old window arrow result
  Nonempty (Derivation body [] ((domain comp context sigma tau f a).imp
    (existsApplication comp context sigma tau f a)))

def ActualOriginalFunctionality : Prop :=
  ∀ (body : Positive (Fin 1)) (old : JointGammaComputability.Data)
    (window : Program 1) (arrow : Program 2) (result : Program 5)
    (context : Nat) (sigma tau : Ty),
  evaluate window (List.Vector.ofFn ![context]) = 1 →
  evaluate arrow (List.Vector.ofFn ![typeNumber sigma,typeNumber tau]) = typeNumber (.arrow sigma tau) →
  ∀ (α : Type) (f a out other : OTerm α),
  let comp := InternalApplication.computability old window arrow result
  Nonempty (Derivation body [] ((domain comp context sigma tau f a).imp
    ((InternalApplication.literalApplication comp.application context sigma tau f a out ⊓
      InternalApplication.literalApplication comp.application context sigma tau f a other).imp
      (equal out other))))

/-- ONE calibrated pair precedes ALL subtype-closed windows and open terms.
The same pair retains typed R-closure, ground C downward closure and the
arbitrary-context Gamma guard transport, and has literal application totality
and raw output uniqueness on the original typed/same-Gamma domain. -/
def ActualUniformApplicationClosureExists : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
  ∃ (src : SourcePresentation.Data) (comp : JointGammaComputability.Data),
  ContextUniform.Calibrated src n arity ∧
  JointGammaComputability.Calibrated comp n arity ∧
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
        ((domain comp context sigma tau f a).imp (existsApplication comp context sigma tau f a)))) ∧
    (∀ (sigma tau : Ty) (f a out other : OTerm α),
      Nonempty (Derivation (SourcePresentation.sourceBody src context) []
        ((domain comp context sigma tau f a).imp
          ((InternalApplication.literalApplication comp.application context sigma tau f a out ⊓
            InternalApplication.literalApplication comp.application context sigma tau f a other).imp
            (equal out other)))))) ∧
  (∀ (context : Nat) (α : Type) (typ x y u : OTerm α),
    Nonempty (Derivation (SourcePresentation.sourceBody src context) []
      (((GuardedSource.literalTyped comp context typ x ⊓ GuardedSource.literalR src context x y) ⊓
        GammaGuardedSource.literalGuard comp y u).imp (GammaGuardedSource.literalGuard comp x u))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationGuardedTargets
