module
public import LogicLineages.PersistentMarking.NumberedWindowInternalScratchMemoThinLookupChecks
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralEnrichedEdgeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairGraphProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedContextMemoProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover programCases)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue programRename valueUnique outputTransport)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalLessThanSupportProof (zeroConstantValue)
open ID1Completion.InternalOriginalOrderSyntaxProof (addRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePair (pair pairTerm)
open NumberedWindowInternalSparsePairGraphProof (pairGraph)
open NumberedWindowInternalSparseFieldParser (scratchRow scratchTable)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename binaryInputsRename)
open NumberedWindowInternalScratchMemoThinLookupChecks (tableLookup)
open ID1Completion.InternalRawListRecursionSyntaxProof (lookupGraph lookupRename)
open NumberedWindowInternalSparsePathEnvelopeTargets (z)
open ID1Completion.InternalTagArithmeticSyntaxProof (zRelabel)
open ID1Completion.InternalRawListRecursion (lookup)
open NumberedWindowInternalLiteralEnrichedEdgeProof (D)

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- The lexical context is a literal passive recursion parameter. Neither
table lookup nor selection resets it when switching from a parent raw pair
to the smaller pair. The unused second parameter is physically zero. -/
def contextualPair : Program 3 :=
  .composition pair (Fin.cons (.projection 1) (Fin.cons (.projection 2) Fin.elim0))

def selectedContextMemo (R : Program 4) : Program 3 :=
  .composition (scratchRow (constantZero 2) R)
    (Fin.cons contextualPair (Fin.cons (.projection 0) (Fin.cons (constantZero 3) Fin.elim0)))

def contextualRow {α : Type} (R : Program 4) (out ctx key : OTerm α) : Formula α :=
  programGraph (scratchRow (constantZero 2) R) out ![key,ctx,z]

def contextualTable {α : Type} (R : Program 4) (out ctx key : OTerm α) : Formula α :=
  programGraph (scratchTable (constantZero 2) R) out ![key,ctx,z]

private theorem contextualPairValue (ctx a b : OTerm α) :
    D B Γ (programGraph contextualPair (pairTerm a b) ![ctx,a,b]) := by
  let xs : Fin 3 → OTerm α := ![ctx,a,b]
  apply compositionValue pair (Fin.cons (.projection 1) (Fin.cons (.projection 2) Fin.elim0))
    (pairTerm a b) xs ![a,b] (pairGraph a b)
  exact fun i => Fin.cases (projectionValue 1 xs) (Fin.cases (projectionValue 2 xs) (fun j => Fin.elim0 j)) i

theorem exact_OpenSelectedContextMemo (R : Program 4) (out ctx q r : OTerm α) :
    D B Γ (programGraph (selectedContextMemo R) out ![ctx,q,r]) ↔
      D B Γ (contextualRow R out ctx (pairTerm q r)) := by
  let xs : Fin 3 → OTerm α := ![ctx,q,r]
  let vs : Fin 3 → OTerm α := ![pairTerm q r,ctx,z]
  let ps : Fin 3 → Program 3 :=
    Fin.cons contextualPair (Fin.cons (.projection 0) (Fin.cons (constantZero 3) Fin.elim0))
  have reports : ∀ i, D B Γ (programGraph (ps i) (vs i) xs) := fun i =>
    Fin.cases (contextualPairValue ctx q r)
      (Fin.cases (projectionValue 0 xs)
        (Fin.cases (zeroConstantValue xs) (fun j => Fin.elim0 j))) i
  constructor
  · intro actual
    exact compositionRecover (scratchRow (constantZero 2) R) ps out xs vs actual reports
  · intro actual
    exact compositionValue (scratchRow (constantZero 2) R) ps out xs vs actual reports

/-- Actual table lookup at an additive difference and actual selection
at that smaller index have the same graph value in both directions. The
converse uses totality at the smaller index and object functionality. -/
theorem exact_OpenContextMemoLookup (R : Program 4) (out ctx key gap table : OTerm α)
    (actual : D B Γ (contextualTable R table ctx (OrdinaryArithmetic.addTerm key gap))) :
    D B Γ (lookupGraph out gap table) ↔ D B Γ (contextualRow R out ctx key) := by
  constructor
  · intro known
    apply programCases (scratchRow (constantZero 2) R) ![key,ctx,z] _
    intro β j Δ v keep row
    simp only [contextualRow,programRename,tripleInputsRename,zRelabel]
    simp only [tripleInputsRename,zRelabel] at row
    have tab := renameInto actual j Δ keep
    simp only [contextualTable,programRename,tripleInputsRename,zRelabel,addRelabel] at tab
    have value := renameInto known j Δ keep
    rw [lookupRename] at value
    let k := key.relabel j
    let c := ctx.relabel j
    let g := gap.relabel j
    let t := table.relabel j
    have observed := tableLookup (constantZero 2) R v k g t ![c,z] row tab
    have eq := valueUnique lookup v (out.relabel j) ![g,t] observed value
    exact outputTransport (scratchRow (constantZero 2) R) v (out.relabel j) ![k,c,z] eq row
  · intro known
    exact tableLookup (constantZero 2) R out key gap table ![ctx,z] known actual

#print axioms exact_OpenSelectedContextMemo
#print axioms exact_OpenContextMemoLookup
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedContextMemoProof
