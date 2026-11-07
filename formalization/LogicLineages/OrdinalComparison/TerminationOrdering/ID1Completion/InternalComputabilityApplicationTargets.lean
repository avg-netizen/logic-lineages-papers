module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityApplicationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityApplicationTargets
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalComputabilityApplication
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

def ActualOriginalComputabilityTypedness : Prop :=
  ∀ (body : Positive (Fin 1)) (data : JointGammaComputability.Data) (α : Type)
    (tau : Ty) (context t : OTerm α),
  Nonempty (Derivation body [] ((computable data tau context t).imp (typed data tau context t)))

/-- Exact arrow elimination, including its original same-Gamma guard and
the original existential application graph with a computable result. -/
def ActualOriginalArrowElimination : Prop :=
  ∀ (body : Positive (Fin 1)) (data : JointGammaComputability.Data) (α : Type)
    (sigma tau : Ty) (context f a : OTerm α),
  Nonempty (Derivation body [] ((premises data sigma tau context f a).imp
    (resultExists data sigma tau context f a)))

/-- Any accepted RAW output of the original active application checker is
computable. No accessibility or computability closure is a caller premise. -/
def ActualOriginalActiveApplicationComputability : Prop :=
  ∀ (body : Positive (Fin 1)) (old : JointGammaComputability.Data)
    (window : Program 1) (arrow : Program 2) (result : Program 5) (α : Type)
    (sigma tau : Ty) (context f a out : OTerm α),
  let data := InternalApplication.computability old window arrow result
  Nonempty (Derivation body [] ((activationAt old window arrow context sigma tau f a).imp
    ((premises data sigma tau context f a).imp
      ((accepted data sigma tau context f a out).imp (computable data tau context out)))))

/-- The literal original builder graph supplies the result; the internal
application theorem establishes computability at that same raw code. -/
def ActualOriginalActiveResultComputability : Prop :=
  ∀ (body : Positive (Fin 1)) (old : JointGammaComputability.Data)
    (window : Program 1) (arrow : Program 2) (result : Program 5) (α : Type)
    (sigma tau : Ty) (context f a out : OTerm α),
  let data := InternalApplication.computability old window arrow result
  Nonempty (Derivation body [] ((activationAt old window arrow context sigma tau f a).imp
    ((premises data sigma tau context f a).imp
      ((programGraph result out (arguments context sigma tau f a)).imp
        (computable data tau context out)))))

/-- Derive activation from its original arithmetic checks and the typedness
already present in the two computability formulas. -/
def ActualOriginalActivationBridge : Prop :=
  ∀ (body : Positive (Fin 1)) (data : JointGammaComputability.Data)
    (window : Program 1) (arrow : Program 2) (α : Type)
    (sigma tau : Ty) (context f a : OTerm α),
  Nonempty (Derivation body [] ((metadata window arrow context sigma tau).imp
    ((premises data sigma tau context f a).imp
      (activationAt data window arrow context sigma tau f a))))

/-- Integrated application: the activation graph is derived internally from
the displayed window/type-code facts, rather than assumed. -/
def ActualOriginalApplicationComputability : Prop :=
  ∀ (body : Positive (Fin 1)) (old : JointGammaComputability.Data)
    (window : Program 1) (arrow : Program 2) (result : Program 5) (α : Type)
    (sigma tau : Ty) (context f a out : OTerm α),
  let data := InternalApplication.computability old window arrow result
  Nonempty (Derivation body [] ((metadata window arrow context sigma tau).imp
    ((premises data sigma tau context f a).imp
      ((accepted data sigma tau context f a out).imp (computable data tau context out)))))

def ActualOriginalResultComputability : Prop :=
  ∀ (body : Positive (Fin 1)) (old : JointGammaComputability.Data)
    (window : Program 1) (arrow : Program 2) (result : Program 5) (α : Type)
    (sigma tau : Ty) (context f a out : OTerm α),
  let data := InternalApplication.computability old window arrow result
  Nonempty (Derivation body [] ((metadata window arrow context sigma tau).imp
    ((premises data sigma tau context f a).imp
      ((programGraph result out (arguments context sigma tau f a)).imp
        (computable data tau context out)))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityApplicationTargets
