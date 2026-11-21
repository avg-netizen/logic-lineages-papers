module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedSeenDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedFilter
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open LogicLineages.ComputabilityKnowledge GorbowPRProgram
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (branch constantZero)
open ID1Completion.InternalListCodec (consCode)
open ID1Completion.InternalRawListRecursion (listRec)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open GorbowVerifierNormalization (normalize)
open SourceComputabilityFormulaSupportProof (existsOne)
open NumberedWindowInternalSparseDirectedSeen (scan scanGraph)

abbrev passTape {T : Type} (vertices seen ctx ty : T) : Fin 4 → T := ![vertices,seen,ctx,ty]
abbrev filterTape {T : Type} (v rest seen ctx ty : T) : Fin 5 → T := ![v,rest,seen,ctx,ty]

/-- From [v,actual filtered tail,seen,ctx,ty] select the original fixed
seen, ctx, ty and this occurrence v, in that order. -/
def scanHead (E : Program 4) : Program 5 :=
  .composition (scan E) ![.projection 2,.projection 3,.projection 4,.projection 0]

/-- Prepend this one literal occurrence to the actual filtered tail. -/
def prependHead : Program 5 :=
  .composition consCode ![.projection 0,.projection 1]

/-- Skip the head on rejection, otherwise retain it in its original order.
The previous output is never substituted for the fixed seen input. -/
def filterStep (E : Program 4) : Program 5 :=
  branch (normalize (scanHead E)) (.projection 1) prependHead

/-- One right-to-left physical pass of the literal source filter. Nil emits
the scratch nil; selected heads are prepended, not appended to seen. -/
def pass (E : Program 4) : Program 4 :=
  listRec (constantZero 3) (filterStep E)

abbrev cell {α : Type} (code h t : OTerm α) : Formula α :=
  programGraph consCode code ![h,t]

def passGraph (E : Program 4) {α : Type} (out vertices seen ctx ty : OTerm α) : Formula α :=
  programGraph (pass E) out (passTape vertices seen ctx ty)

def restRow (E : Program 4) {α : Type} (out h tail rest seen ctx ty : OTerm α) : Formula α :=
  passGraph E rest tail seen ctx ty ⊓
    ((scanGraph E seen ctx ty h ⊓ cell out h rest) ⊔
      ((scanGraph E seen ctx ty h).not ⊓ eqn out rest))

/-- Both branches share one genuine result of filtering this actual tail. -/
def restReport (E : Program 4) {α : Type} (out h tail seen ctx ty : OTerm α) : Formula α :=
  let j : α → α ⊕ Fin 1 := Sum.inl
  existsOne (restRow E (out.relabel j) (h.relabel j) (tail.relabel j) (.var (.inr 0))
    (seen.relabel j) (ctx.relabel j) (ty.relabel j))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedFilter
