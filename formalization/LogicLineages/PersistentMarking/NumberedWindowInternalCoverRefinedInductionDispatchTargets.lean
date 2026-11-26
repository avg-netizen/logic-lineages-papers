module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverOwnEarlierTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedValidityCasesTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNamedLeafTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarTypeLeafTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNumberedOwnTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedInductionDispatchTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (Reports)
open NumberedWindowInternalSparseFieldCell (cellTail)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (headsTerm typesTerm measurePair)
open NumberedWindowInternalCoverSelectedGrammarWidthTargets (observed)
open NumberedWindowInternalCoverSelectedGrammarAuxScratchTargets (selectedCover)
open NumberedWindowInternalCoverNamedLeavesTargets (namedTerm)
open NumberedWindowInternalCoverTypeLeavesTargets (typeLeafTerm)
open NumberedWindowInternalCoverLambdaLayerTargets (lambdaTerm)
open NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnTargets (ordinaryKey)
open NumberedWindowInternalCoverSelectedGrammarNumberedOwnTargets (BoundedNumberedArgs)
open NumberedWindowInternalCoverNumberedLayerTargets (numberedTerm)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalCoverSelectedValidityTargets (headerAt)
open NumberedWindowInternalCoverOwnEarlierTargets (ownBelow)
open NumberedWindowInternalCoverLocalOwnContinuationTargets (ActualOwnParent)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalCoverRefinedSharedSyntaxTargets (refinedSyntax)
open NumberedWindowInternalCoverSharedRecursionTargets (sharedMeasureUpdate)
open NumberedWindowInternalStrictAuxWindowTargets (strictAuxWindow)

structure Programs where
  V : Program 1
  R : Program 4
  W : Program 3

abbrev Programs.cover (P : Programs) : Program 3 := selectedCover P.V (selectedMeasure P.R)

def refinedPrograms (V TV M : Program 1) (B : Program 2) (TW : Program 1) : Programs :=
  ⟨refinedSyntax V TV,sharedMeasureUpdate M,strictAuxWindow B TW⟩

/-- One real contextual parent and its actual finite own-cover scratch.
The below formula is the original bounded induction condition. -/
structure ParentRow (P : Programs) (s : Settings) (body : Positive (Fin 1))
    {α : Type} (Γ : List (Formula α)) (key p vertices ctx result : OTerm α) : Prop where
  parent : ActualOwnParent P.V P.R s body Γ key p vertices
  typed : Nonempty (Derivation body Γ (windowAt P.W ctx result key))
  branchBelow : Nonempty (Derivation body Γ (ownBelow P.V P.W P.cover s key))

/-- Keep the original raw term and ordered physical reports, even once
the parent, typed graph and below formula are moved to the literal code. -/
structure PackedRow (P : Programs) (s : Settings) (body : Positive (Fin 1))
    {α : Type} (Γ : List (Formula α)) (raw key p vertices ctx result : OTerm α)
    (tag : Nat) (fields : List (OTerm α)) : Prop where
  data : ParentRow P s body Γ key p vertices ctx result
  ordered : Reports body Γ raw cellTail fields
  packed : Nonempty (Derivation body Γ (eqn raw key))
  header : Nonempty (Derivation body Γ (headerAt tag fields.length raw))

/-- Allow indispensable original witnesses to be supplied under their
actual object binders. Their terms cannot escape the given goal. -/
def Supplies (body : Positive (Fin 1)) {α : Type} (Γ : List (Formula α))
    (goal : Formula α) (Data : ∀ (β : Type), (α → β) → List (Formula β) → Prop) : Prop :=
  (∀ (β : Type) (j : α → β) (Δ : List (Formula β)),
    (∀ f ∈ Γ, f.relabel j ∈ Δ) → Data β j Δ →
    Nonempty (Derivation body Δ (goal.relabel j))) →
  Nonempty (Derivation body Γ goal)

def NamedFacts (s : Settings) (body : Positive (Fin 1)) {α : Type} (Γ : List (Formula α))
    (p ty i : OTerm α) : Prop :=
  ∃ d width : OTerm α,
    Nonempty (Derivation body Γ (measurePair p d width)) ∧
    Nonempty (Derivation body Γ (memberGraph (typesTerm s α) ty)) ∧
    Nonempty (Derivation body Γ (ltF i (suc width)))

def TypeFacts (s : Settings) (body : Positive (Fin 1)) {α : Type} (Γ : List (Formula α))
    (p ty : OTerm α) : Prop :=
  ∃ d width : OTerm α,
    Nonempty (Derivation body Γ (measurePair p d width)) ∧
    Nonempty (Derivation body Γ (memberGraph (typesTerm s α) ty))

def LambdaFacts (W : Program 3) (s : Settings) (body : Positive (Fin 1))
    {α : Type} (Γ : List (Formula α)) (ctx result ty q : OTerm α) : Prop :=
  ∃ bodyTy : OTerm α,
    Nonempty (Derivation body Γ (eqn result (rawCons ty bodyTy))) ∧
    Nonempty (Derivation body Γ (windowAt W (rawCons ty ctx) bodyTy q)) ∧
    Nonempty (Derivation body Γ (memberGraph (typesTerm s α) ty))

def OrdinaryFacts (s : Settings) (body : Positive (Fin 1)) {α : Type} (Γ : List (Formula α))
    (p h a : OTerm α) : Prop :=
  ∃ d width da wa state terms args : OTerm α,
    Nonempty (Derivation body Γ (measurePair p d width)) ∧
    BoundedNumberedArgs body Γ d (headsTerm s α) (typesTerm s α) width da wa state terms args a ∧
    Nonempty (Derivation body Γ (memberGraph (headsTerm s α) h))

def NumberedFacts (s : Settings) (body : Positive (Fin 1)) {α : Type} (Γ : List (Formula α))
    (p h ty k l r : OTerm α) : Prop :=
  ∃ d width dl wl ls lt la dr wr rs rt ra : OTerm α,
    Nonempty (Derivation body Γ (measurePair p d width)) ∧
    BoundedNumberedArgs body Γ d (headsTerm s α) (typesTerm s α) width dl wl ls lt la l ∧
    BoundedNumberedArgs body Γ d (headsTerm s α) (typesTerm s α) width dr wr rs rt ra r ∧
    Nonempty (Derivation body Γ (memberGraph (headsTerm s α) h)) ∧
    Nonempty (Derivation body Γ (memberGraph (typesTerm s α) ty)) ∧
    Nonempty (Derivation body Γ (ltF k (suc width)))

/-- Explicit remaining provenance obligations, not placeholders for a
parent membership conclusion. All receive the same actual packed row;
the five measured branches must use the very same given measure code. -/
structure Obligations (P : Programs) (s : Settings) (body : Positive (Fin 1)) : Prop where
  named : ∀ (b : Bool) (α : Type) (Γ : List (Formula α)) (raw p vertices ctx result ty i : OTerm α)
    (goal : Formula α),
    PackedRow P s body Γ raw (namedTerm b.toNat ty i) p vertices ctx result b.toNat [ty,i] →
    Supplies body Γ goal (fun β j Δ => NamedFacts s body Δ (p.relabel j) (ty.relabel j) (i.relabel j))
  lambdaBody : ∀ (α : Type) (Γ : List (Formula α)) (raw p vertices ctx result ty q : OTerm α)
    (goal : Formula α),
    PackedRow P s body Γ raw (lambdaTerm ty q) p vertices ctx result 2 [ty,q] →
    Supplies body Γ goal (fun β j Δ => LambdaFacts P.W s body Δ
      (ctx.relabel j) (result.relabel j) (ty.relabel j) (q.relabel j))
  typeLeaf : ∀ (α : Type) (Γ : List (Formula α)) (raw p vertices ctx result ty : OTerm α)
    (goal : Formula α),
    PackedRow P s body Γ raw (typeLeafTerm ty) p vertices ctx result 3 [ty] →
    Supplies body Γ goal (fun β j Δ => TypeFacts s body Δ (p.relabel j) (ty.relabel j))
  ordinary : ∀ (α : Type) (Γ : List (Formula α)) (raw p vertices ctx result h a : OTerm α)
    (goal : Formula α),
    PackedRow P s body Γ raw (ordinaryKey h a) p vertices ctx result 4 [h,a] →
    Supplies body Γ goal (fun β j Δ => OrdinaryFacts s body Δ (p.relabel j) (h.relabel j) (a.relabel j))
  numbered : ∀ (α : Type) (Γ : List (Formula α)) (raw p vertices ctx result h ty k l r : OTerm α)
    (goal : Formula α),
    PackedRow P s body Γ raw (numberedTerm h ty k l r) p vertices ctx result 5 [h,ty,k,l,r] →
    Supplies body Γ goal (fun β j Δ => NumberedFacts s body Δ (p.relabel j)
      (h.relabel j) (ty.relabel j) (k.relabel j) (l.relabel j) (r.relabel j))
  auxTypes : ∀ (α : Type) (Γ : List (Formula α)) (raw p vertices ctx result dom cod fn arg : OTerm α),
    PackedRow P s body Γ raw (auxiliaryTerm dom cod fn arg) p vertices ctx result 6 [dom,cod,fn,arg] →
    Nonempty (Derivation body Γ (memberGraph (typesTerm s α) dom)) ∧
    Nonempty (Derivation body Γ (memberGraph (typesTerm s α) cod))

def ExactOpenCoverRefinedInductionDispatch : Prop :=
  ∀ (V TV M : Program 1) (B : Program 2) (TW : Program 1) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (raw p vertices ctx result : OTerm α),
    let P := refinedPrograms V TV M B TW
    Obligations P s body →
    ParentRow P s body Γ raw p vertices ctx result →
    Nonempty (Derivation body Γ (memberGraph vertices raw))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedInductionDispatchTargets
