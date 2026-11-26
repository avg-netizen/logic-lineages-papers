module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedFilterDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedRounds
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open LogicLineages.ComputabilityKnowledge GorbowPRProgram
open InternalAcceptance (constantZero)
open InternalListCodec (consCode)
open InternalRawListRecursion (listRec)
open NumberedWindowInternalSparseDirectedFilter (pass)

abbrev roundsTape {T : Type} (fuel vertices ctx ty seed : T) : Fin 5 → T :=
  ![fuel,vertices,ctx,ty,seed]

abbrev membersTape {T : Type} (vertices ctx ty seed : T) : Fin 4 → T :=
  ![vertices,ctx,ty,seed]

/-- The literal standard scratch cons of the actual seed onto nil. -/
def singletonSeed : Program 4 :=
  .composition consCode ![.projection 3,constantZero 4]

/-- The zero round filters the same original vertices against just the
actual seed, without inserting it into a pool where it does not occur. -/
def roundBase : Program 4 :=
  .composition (pass (constantZero 4)) ![.projection 0,singletonSeed,.projection 1,.projection 2]

/-- On [counter,seen,vertices,ctx,ty,seed], the original vertices and the
actual preceding round are different slots; context and type are fixed. -/
def roundStep (E : Program 4) : Program 6 :=
  .composition (pass E) ![.projection 2,.projection 1,.projection 3,.projection 4]

def rounds (E : Program 4) : Program 5 :=
  .recursion roundBase (roundStep E)

/-- Count the actual supplied ordered scratch pool, including repeats. -/
def poolLength : Program 1 :=
  listRec (constantZero 0) (.composition .succ (fun _ : Fin 1 => .projection 1))

def selectedFuel : Program 4 :=
  .composition poolLength (fun _ : Fin 1 => .projection 0)

/-- Use the length of the unchanged supplied vertices as the exact fuel. -/
def members (E : Program 4) : Program 4 :=
  .composition (rounds E) ![selectedFuel,.projection 0,.projection 1,.projection 2,.projection 3]

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedRounds
