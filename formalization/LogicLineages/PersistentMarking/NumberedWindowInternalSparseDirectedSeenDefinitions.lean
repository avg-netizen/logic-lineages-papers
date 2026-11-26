module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceComputabilityFormulaSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedSeen
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram
open SourceComputabilityFormulaSupportProof (existsOne)
open ID1Completion.InternalAcceptance (branch constantZero)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalLessThan (constantOne)
open ID1Completion.InternalRawListRecursion (listRec)
open GorbowVerifierNormalization (normalize)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)

abbrev scanTape {T : Type} (seen ctx ty v : T) : Fin 4 → T := ![seen,ctx,ty,v]
abbrev edgeTape {T : Type} (ctx ty w v : T) : Fin 4 → T := ![ctx,ty,w,v]
abbrev rowTape {T : Type} (w prev ctx ty v : T) : Fin 5 → T := ![w,prev,ctx,ty,v]

/-- At the actual row [w,prior tail result,ctx,ty,v], compare w and v. -/
def headEq : Program 5 :=
  .composition equalityTest ![.projection 0,.projection 4]

/-- At that same row, call E on [ctx,ty,w,v], not on the reverse edge. -/
def edgeCall (E : Program 4) : Program 5 :=
  .composition E ![.projection 2,.projection 3,.projection 0,.projection 4]

/-- Literal directed row. Equality is sufficient; otherwise exact-one
acceptance of E is sufficient. When neither holds, retain the actual
recursive tail result rather than manufacturing a witness or a new list. -/
def scanStep (E : Program 4) : Program 5 :=
  branch (normalize headEq)
    (branch (normalize (edgeCall E)) (.projection 1) (constantOne 5))
    (constantOne 5)

/-- Literal standard-scratch list recursion. At nil the three unchanged
parameters do not create a witness. -/
def scan (E : Program 4) : Program 4 :=
  listRec (constantZero 3) (scanStep E)

def scanGraph (E : Program 4) {α : Type} (seen ctx ty v : OTerm α) : Formula α :=
  programGraph (scan E) (suc z) (scanTape seen ctx ty v)

def acceptEdge (E : Program 4) {α : Type} (ctx ty w v : OTerm α) : Formula α :=
  programGraph E (suc z) (edgeTape ctx ty w v)

def witnessRow (E : Program 4) {α : Type} (seen ctx ty w v : OTerm α) : Formula α :=
  memberGraph seen w ⊓ (eqn w v ⊔ acceptEdge E ctx ty w v)

/-- The same bound occurrence appears in membership and in the directed
row test, and every free input is retained under the original binder. -/
def seenWitness (E : Program 4) {α : Type} (seen ctx ty v : OTerm α) : Formula α :=
  let j : α → α ⊕ Fin 1 := Sum.inl
  existsOne (witnessRow E (seen.relabel j) (ctx.relabel j) (ty.relabel j)
    (.var (.inr 0)) (v.relabel j))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedSeen
