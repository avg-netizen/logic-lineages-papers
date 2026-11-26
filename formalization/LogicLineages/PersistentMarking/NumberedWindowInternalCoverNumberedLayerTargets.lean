module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentCellsTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedLayerTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalFiniteBlocks (block)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalListCodec (consCode)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn z)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedMultisetNumeric (numbersNumber)
open NumberedWindowCoverAlgorithm (numbered)
open NumberedWindowInternalSparsePair (fieldCons)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalCoverCartesianFoldTargets (flatMap)
open NumberedWindowInternalCoverAuxApplicationsTargets (binary reorder)
open NumberedWindowInternalCoverArgumentCellsTargets (axisInclusion)

/-- Sparse tag 5 with original field order [head,type,id,prefix,suffix].
The surrounding scratch singleton uses the separate standard cons. -/
def numberedTerm {α : Type} (h ty idArg leftArgs rightArgs : OTerm α) : OTerm α :=
  rawCons (numeral 5) (rawCons h (rawCons ty (rawCons idArg (rawCons leftArgs (rawCons rightArgs z)))))

/-- Inputs [suffix,head,type,id,prefix]. -/
def numberedCode : Program 5 :=
  binary fieldCons (literal 5 5)
    (binary fieldCons (.projection 1)
      (binary fieldCons (.projection 2)
        (binary fieldCons (.projection 3)
          (binary fieldCons (.projection 4)
            (binary fieldCons (.projection 0) (constantZero 5))))))

def singletonNumbered : Program 5 := binary consCode numberedCode (constantZero 5)

/-- At a selected prefix, fold the remaining suffix axis:
[prefix,args,head,type,id] goes to [args,head,type,id,prefix]. -/
def prefixBlock : Program 5 := reorder (flatMap singletonNumbered) ![1,2,3,4,0]

/-- At a selected id, fold both argument axes over the *same* original
scratch: [id,args,head,type] goes to [args,args,head,type,id]. -/
def idBlock : Program 4 := reorder (flatMap prefixBlock) ![1,1,2,3,0]

/-- At a selected type, [type,ids,args,head] goes to [ids,args,head,type]. -/
def typeBlock : Program 4 := reorder (flatMap idBlock) ![1,2,3,0]

/-- At a selected head, [head,types,ids,args] goes to [types,ids,args,head]. -/
def headBlock : Program 4 := reorder (flatMap typeBlock) ![1,2,3,0]

/-- The five source axes are H, K, numeral IDs, prefix args, suffix args
in original occurrence order. This accepts an actual IDs list, not a
hidden recomputed bound. -/
def numberedLayer : Program 4 := flatMap headBlock

abbrev numberedReport {α : Type} (out H K ids args : OTerm α) : Formula α :=
  programGraph numberedLayer out ![H,K,ids,args]

def ExactCoverNumberedLayerValue : Prop :=
  ∀ (H K ids args : List Nat),
    evaluate numberedLayer (numbersNumber H ::ᵥ numbersNumber K ::ᵥ numbersNumber ids ::ᵥ numbersNumber args ::ᵥ nil) =
      numbersNumber (numbered H K ids args)

def ExactOpenCoverNumberedLayerConstructor : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (out H K ids args h ty k l r : OTerm α),
  Nonempty (Derivation body Γ (numberedReport out H K ids args)) →
  Nonempty (Derivation body Γ (memberGraph H h)) →
  Nonempty (Derivation body Γ (memberGraph K ty)) →
  Nonempty (Derivation body Γ (memberGraph ids k)) →
  Nonempty (Derivation body Γ (memberGraph args l)) →
  Nonempty (Derivation body Γ (memberGraph args r)) →
  Nonempty (Derivation body Γ (memberGraph out (numberedTerm h ty k l r)))

abbrev numberedOriginRow {α : Type} (H K ids args key h ty k l r : OTerm α) : Formula α :=
  memberGraph H h ⊓ (memberGraph K ty ⊓ (memberGraph ids k ⊓
    (memberGraph args l ⊓ (memberGraph args r ⊓ eqn (numberedTerm h ty k l r) key))))

abbrev numberedOriginMatrix {α : Type} (H K ids args key : OTerm α) : Formula (α ⊕ Fin 5) :=
  numberedOriginRow (H.relabel Sum.inl) (K.relabel Sum.inl) (ids.relabel Sum.inl) (args.relabel Sum.inl)
    (key.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3)) (.var (.inr 4))

abbrev numberedOrigin {α : Type} (H K ids args key : OTerm α) : Formula α :=
  block (numberedOriginMatrix H K ids args key)

def ExactOpenCoverNumberedLayerOrigin : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (out H K ids args key : OTerm α),
  Nonempty (Derivation body Γ (numberedReport out H K ids args)) →
  Nonempty (Derivation body Γ (memberGraph out key)) →
  Nonempty (Derivation body Γ (numberedOrigin H K ids args key))

/-- Two actual reports on the same head and type lists. Only actual ID
inclusion and shared-argument-list inclusion are required, not any whole
grammar-stage statement. -/
def ExactOpenCoverNumberedLayerTransport : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (old next H K ids ids' args args' key : OTerm α),
  Nonempty (Derivation body Γ (numberedReport old H K ids args)) →
  Nonempty (Derivation body Γ (numberedReport next H K ids' args')) →
  Nonempty (Derivation body Γ (axisInclusion ids ids')) →
  Nonempty (Derivation body Γ (axisInclusion args args')) →
  Nonempty (Derivation body Γ (memberGraph old key)) →
  Nonempty (Derivation body Γ (memberGraph next key))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedLayerTargets
