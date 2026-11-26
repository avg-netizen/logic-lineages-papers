module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelope

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowFieldAlgorithm (unpackNode)
open NumberedWindowPositivePathAlgorithm (edgeView hopView)
open NumberedWindowInternalSparsePair (pairTerm)
open NumberedWindowInternalSparsePathEnvelope

def AllInputTaggedNode : Prop := ∀ n, selectedNode n = unpackNode n
def AllInputEdgeEnvelope : Prop := ∀ n, selectedEdge n = edgeView n
def AllInputHopEnvelope : Prop := ∀ n, selectedHop n = hopView n

abbrev z {α : Type} : OTerm α := OrdinaryArithmetic.zeroTerm
abbrev suc {α : Type} (x : OTerm α) : OTerm α := OrdinaryArithmetic.succTerm x

/-- Exact ordinary-arithmetic encoding, independent of the guard and
selectors. The empty list is zero, not an arbitrary final cursor. -/
def rawCons {α : Type} (h t : OTerm α) : OTerm α := suc (pairTerm h t)

def edgeCodeTerm {α : Type} (q w r : OTerm α) : OTerm α :=
  rawCons (suc z) (rawCons q (rawCons r (rawCons w z)))

def hopCodeTerm {α : Type} (t q w r : OTerm α) : OTerm α :=
  rawCons (suc (suc z)) (rawCons t (rawCons (edgeCodeTerm q w r) z))

def unary {α : Type} (p : Program 1) (out code : OTerm α) : Formula α :=
  programGraph p out ![code]

def edgeCertified {α : Type} (n q w r : OTerm α) : Formula α :=
  unary edgeGood (suc z) n ⊓
    (unary edgeSource q n ⊓ (unary edgeWitness w n ⊓ unary edgeTarget r n))

def hopCertified {α : Type} (n t q w r : OTerm α) : Formula α :=
  unary hopGood (suc z) n ⊓
    (unary hopTarget t n ⊓
      (unary hopSource q n ⊓ (unary hopWitness w n ⊓ unary hopRawTarget r n)))

def OpenEdgeEnvelope : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (n q w r : OTerm α),
    let e := equal n (edgeCodeTerm q w r)
    let a := edgeCertified n q w r
    Nonempty (Derivation body [] ((e.imp a) ⊓ (a.imp e)))

def OpenHopEnvelope : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (n t q w r : OTerm α),
    let e := equal n (hopCodeTerm t q w r)
    let a := hopCertified n t q w r
    Nonempty (Derivation body [] ((e.imp a) ⊓ (a.imp e)))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeTargets
