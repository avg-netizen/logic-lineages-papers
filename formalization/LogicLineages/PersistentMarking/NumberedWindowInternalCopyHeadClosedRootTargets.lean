module
public import LogicLineages.PersistentMarking.NumberedWindowInternalCopyHeadConeTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunRootTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCopyHeadClosedRootTargets
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowCopyAlgorithm (Entries rank)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowFieldAlgorithm (packNode unpackNode)
open NumberedWindowAnnotationAlgorithm (declaration)
open NumberedWindowInternalSparseRawTickTargets (ActualRoot)
open NumberedWindowInternalSparseTypedRaw (typedRaw5)
open NumberedWindowInternalSparseRawRunRootTargets (rootWitnessTerm)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalConstructorHeadFiniteTargets (D)

def copyPayload : Nat := packNode 3 []

abbrev concreteCopyRoot (entries : Entries) (s : Settings) :=
  NumberedWindowConcreteCheckers.root entries s

def RootCone (entries : Entries) (s : Settings) (B : Positive (Fin 1))
    {α : Type} (Γ : List (Formula α)) (src dst f ty label base extras g args : Nat)
    (goal : Formula α) : Prop :=
  unpackNode src = some (5,[f,ty,label,base,extras]) ∧
  unpackNode dst = some (4,[g,args]) ∧
  (g ∈ s.window.2 → ty = (declaration g).1 →
    ∀ rf rg, rank entries f = some rf → rank entries g = some rg →
    D B Γ (ltF (numeral rg) (numeral rf)) → D B Γ goal)

def ExactOriginalClosedCopyRootCone : Prop :=
  ∀ (entries : Entries) (s : Settings) (root : Program 3),
    ActualRoot (concreteCopyRoot entries s) root →
    ∀ (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
      (src dst f ty label base extras g args : Nat) (goal : Formula α),
      D B Γ (programGraph root (suc z) ![numeral src,numeral copyPayload,numeral dst]) →
      RootCone entries s B Γ src dst f ty label base extras g args goal → D B Γ goal

/-- The input context and type remain open object terms. Only the
physical endpoint raw numerals are literal at the rank-extraction cut. -/
def ExactOriginalClosedEndpointTypedCopyCone : Prop :=
  ∀ (entries : Entries) (s : Settings) (root other window : Program 3) (syntaxCode : Program 1),
    ActualRoot (concreteCopyRoot entries s) root →
    ∀ (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
      (ctx result : OTerm α) (src dst f ty label base extras g args : Nat) (goal : Formula α),
      D B Γ (programGraph (typedRaw5 root other window syntaxCode) (suc z)
        ![ctx,result,numeral src,rootWitnessTerm (numeral copyPayload),numeral dst]) →
      RootCone entries s B Γ src dst f ty label base extras g args goal → D B Γ goal

end LogicLineages.PersistentMarking.NumberedWindowInternalCopyHeadClosedRootTargets
