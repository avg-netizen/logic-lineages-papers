module
public import LogicLineages.PersistentMarking.NumberedWindowInternalThinPackedEdgeMutualSeedProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalThinPackedPairState
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename quadInputsRename)
open NumberedWindowInternalSparsePackedLeast (membersAtSeed)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparsePackedLeastOpenSyntaxProof (leastRename)
open NumberedWindowInternalSparseCoverScratch (scratchVertices)
open NumberedWindowInternalSparseScalarEdge (edge4)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge edgeTape)

structure PairPlan (α : Type) where
  ctx : OTerm α
  ty : OTerm α
  a : OTerm α
  b : OTerm α
  va : OTerm α
  vb : OTerm α
  pa : OTerm α
  pb : OTerm α
  x : OTerm α
  y : OTerm α

def PairPlan.map {α β : Type} (p : PairPlan α) (j : α → β) : PairPlan β :=
  ⟨p.ctx.relabel j,p.ty.relabel j,p.a.relabel j,p.b.relabel j,p.va.relabel j,
    p.vb.relabel j,p.pa.relabel j,p.pb.relabel j,p.x.relabel j,p.y.relabel j⟩

def seedReport (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings) {α : Type}
    (ctx ty a va pa x : OTerm α) : Formula α :=
  leastGraph C X W s ctx ty a x ⊓
    (unary (scratchVertices C s) va a ⊓ programGraph (membersAtSeed C X W s) pa ![ctx,ty,a])

theorem seedRename (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings) {α β : Type}
    (ctx ty a va pa x : OTerm α) (j : α → β) :
    (seedReport C X W s ctx ty a va pa x).relabel j =
      seedReport C X W s (ctx.relabel j) (ty.relabel j) (a.relabel j) (va.relabel j)
        (pa.relabel j) (x.relabel j) := by
  simp only [seedReport,conjunctionRename,leastRename,unaryRename,programRename,tripleInputsRename]

def pairReport (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings) {α : Type}
    (p : PairPlan α) : Formula α :=
  seedReport C X W s p.ctx p.ty p.a p.va p.pa p.x ⊓
    (seedReport C X W s p.ctx p.ty p.b p.vb p.pb p.y ⊓ acceptEdge (edge4 X W) p.ctx p.ty p.a p.b)

theorem pairRename (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings) {α β : Type}
    (p : PairPlan α) (j : α → β) :
    (pairReport C X W s p).relabel j = pairReport C X W s (p.map j) := by
  simp only [pairReport,PairPlan.map,conjunctionRename,seedRename,acceptEdge,programRename,edgeTape,
    quadInputsRename,sucRelabel,zRelabel]

#print axioms pairRename
end LogicLineages.PersistentMarking.NumberedWindowInternalThinPackedPairState
