module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedWindowDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawLiftTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalThinApplicationHopTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalFiniteBlocks (block)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseTypedRaw (typedRaw5)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc rawCons)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm functionWitnessTerm)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalMeasuredUnrestrictedWindowDefinitions (window)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparsePositiveHeadDecompositionTargets (positiveAt)
open NumberedWindowInternalSparseAddressSingletonTargets (singletonCertificate)

def rawAt {α : Type} (raw : Program 5) (ctx ty q w r : OTerm α) : Formula α :=
  programGraph raw (suc z) ![ctx,ty,q,w,r]

def premises {α : Type} (raw : Program 5) (W : Program 3)
    (ctx dom cod arg f child g : OTerm α) : Formula α :=
  rawAt raw ctx (rawCons dom cod) f child g ⊓
    (windowAt W ctx cod (auxiliaryTerm dom cod f arg) ⊓ windowAt W ctx cod (auxiliaryTerm dom cod g arg))

def hopData {α : Type} (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (raw : Program 5) (ctx cod src wr dst left right : OTerm α) : Formula α :=
  (leastGraph C X W s ctx cod src left ⊓ leastGraph C X W s ctx cod dst right) ⊓
    positiveAt raw (packedLeastProgram C X W s) ctx cod left (singletonCertificate right src wr dst) right

def row {α : Type} (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (raw : Program 5) (ctx cod src wr dst : OTerm α) : Formula (α ⊕ Fin 2) :=
  let j : α → α ⊕ Fin 2 := Sum.inl
  hopData C X W s raw (ctx.relabel j) (cod.relabel j) (src.relabel j) (wr.relabel j)
    (dst.relabel j) (.var (.inr 0)) (.var (.inr 1))

abbrev provided {α : Type} (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (raw : Program 5) (ctx cod src wr dst : OTerm α) : Formula α :=
  block (row C X W s raw ctx cod src wr dst)

def ExactRawApplicationHop : Prop := ∀ (C root other baseW : Program 3) (V : Program 1) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx dom cod arg f child g : OTerm α),
    let W := window C s baseW V
    let raw := typedRaw5 root other W V
    Nonempty (Derivation body Γ ((premises raw W ctx dom cod arg f child g).imp
      (rawAt raw ctx cod (auxiliaryTerm dom cod f arg) (functionWitnessTerm child) (auxiliaryTerm dom cod g arg))))

def ExactExistentialApplicationHop : Prop := ∀ (C root other baseW : Program 3) (V : Program 1)
    (X : Program 2) (s : Settings) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ctx dom cod arg f child g : OTerm α),
    let W := window C s baseW V
    let raw := typedRaw5 root other W V
    Nonempty (Derivation body Γ ((premises raw W ctx dom cod arg f child g).imp
      (provided C X W s raw ctx cod (auxiliaryTerm dom cod f arg) (functionWitnessTerm child)
        (auxiliaryTerm dom cod g arg))))

end LogicLineages.PersistentMarking.NumberedWindowInternalThinApplicationHopTargets
