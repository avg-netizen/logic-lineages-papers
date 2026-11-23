module
public import LogicLineages.PersistentMarking.NumberedWindowCopyAlgorithm
public import LogicLineages.PersistentMarking.NumberedWindowInternalConstructorHeadFiniteTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCopyHeadConeTargets
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedMultisetNumeric (numbersNumber)
open NumberedWindowCopyAlgorithm (Entries compareRanks copy rank)
open NumberedWindowFieldAlgorithm (unpackNode)
open NumberedWindowAnnotationAlgorithm (declaration)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalConstructorHeadFiniteTargets (D)

def ExactOriginalCopyHeadCone : Prop :=
  ∀ (entries : Entries) (heads : List Nat)
    (src dst srcHead result label base extras dstHead dstBase : Nat),
    unpackNode src = some (5,[srcHead,result,label,base,extras]) →
    unpackNode dst = some (4,[dstHead,dstBase]) →
    copy entries heads src dst = true →
    dstHead ∈ heads ∧ result = (declaration dstHead).1 ∧
      ∃ rankSrc rankDst,
        rank entries srcHead = some rankSrc ∧
        rank entries dstHead = some rankDst ∧ rankDst < rankSrc

/-- This is a calibration of the supplied actual comparison graph,
not an assertion that an arbitrary whole open copy proof exposes it. -/
def CompareFit (entries : Entries) (p : Program 2) : Prop :=
  ∀ f g, evaluate p (f ::ᵥ g ::ᵥ List.Vector.nil) = (compareRanks true entries f g).toNat

def ExactOpenSelectedCopyHeadCone : Prop :=
  ∀ (entries : Entries) (p : Program 2), CompareFit entries p →
  ∀ (heads : List Nat) (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (source target : OTerm α) (goal : Formula α),
    D B Γ (memberGraph (numeral (numbersNumber heads)) source) →
    D B Γ (memberGraph (numeral (numbersNumber heads)) target) →
    D B Γ (programGraph p (suc z) ![source,target]) →
    (∀ f ∈ heads, ∀ g ∈ heads, ∀ rankSrc rankDst,
      rank entries f = some rankSrc →
      rank entries g = some rankDst →
      let Δ := eqn target (numeral g) :: eqn source (numeral f) :: Γ
      D B Δ (ltF (numeral rankDst) (numeral rankSrc)) →
      D B Δ goal) →
    D B Γ goal

end LogicLineages.PersistentMarking.NumberedWindowInternalCopyHeadConeTargets
