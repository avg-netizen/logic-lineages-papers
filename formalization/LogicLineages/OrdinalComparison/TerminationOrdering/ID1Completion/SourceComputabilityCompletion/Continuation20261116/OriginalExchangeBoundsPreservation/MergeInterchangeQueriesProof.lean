module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.MergeInterchangeAtProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.MergeInterchangeQueriesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261115.OriginalBoundsRecombination (maximum merge)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
def sa : Program 3 := .composition InternalUnpair.left (fun _ : Fin 1 => .projection 0)
def la : Program 3 := .composition InternalUnpair.right (fun _ : Fin 1 => .projection 0)
def sb : Program 3 := .composition InternalUnpair.left (fun _ : Fin 1 => .projection 1)
def lb : Program 3 := .composition InternalUnpair.right (fun _ : Fin 1 => .projection 1)
def sc : Program 3 := .composition InternalUnpair.left (fun _ : Fin 1 => .projection 2)
def lc : Program 3 := .composition InternalUnpair.right (fun _ : Fin 1 => .projection 2)
def mbc : Program 3 := .composition maximum ![lb,lc]
def mac : Program 3 := .composition maximum ![la,lc]
def ml : Program 3 := .composition maximum ![la,mbc]
def mr : Program 3 := .composition maximum ![lb,mac]
def queries : Fin 10 → Program 3 := ![sa,la,sb,lb,sc,lc,mbc,mac,ml,mr]

theorem recover (a b c : OTerm alpha) (ys : Fin 10 → OTerm alpha)
    (hq : ∀ i, Nonempty (Derivation body Delta (programGraph (queries i) (ys i) ![a,b,c]))) :
    Nonempty (Derivation body Delta (graph2 InternalPairing.pairing a (ys 0) (ys 1))) ∧
    Nonempty (Derivation body Delta (graph2 InternalPairing.pairing b (ys 2) (ys 3))) ∧
    Nonempty (Derivation body Delta (graph2 InternalPairing.pairing c (ys 4) (ys 5))) ∧
    Nonempty (Derivation body Delta (graph2 maximum (ys 6) (ys 3) (ys 5))) ∧
    Nonempty (Derivation body Delta (graph2 maximum (ys 7) (ys 1) (ys 5))) ∧
    Nonempty (Derivation body Delta (graph2 maximum (ys 8) (ys 1) (ys 6))) ∧
    Nonempty (Derivation body Delta (graph2 maximum (ys 9) (ys 3) (ys 7))) := by
  have h0 := unaryRecover InternalUnpair.left (.projection 0) (ys 0) a ![a,b,c] (hq 0) (projectionValue 0 ![a,b,c])
  have h1 := unaryRecover InternalUnpair.right (.projection 0) (ys 1) a ![a,b,c] (hq 1) (projectionValue 0 ![a,b,c])
  have h2 := unaryRecover InternalUnpair.left (.projection 1) (ys 2) b ![a,b,c] (hq 2) (projectionValue 1 ![a,b,c])
  have h3 := unaryRecover InternalUnpair.right (.projection 1) (ys 3) b ![a,b,c] (hq 3) (projectionValue 1 ![a,b,c])
  have h4 := unaryRecover InternalUnpair.left (.projection 2) (ys 4) c ![a,b,c] (hq 4) (projectionValue 2 ![a,b,c])
  have h5 := unaryRecover InternalUnpair.right (.projection 2) (ys 5) c ![a,b,c] (hq 5) (projectionValue 2 ![a,b,c])
  have h6 := binaryRecover maximum lb lc (ys 6) (ys 3) (ys 5) ![a,b,c] (hq 6) (hq 3) (hq 5)
  have h7 := binaryRecover maximum la lc (ys 7) (ys 1) (ys 5) ![a,b,c] (hq 7) (hq 1) (hq 5)
  have h8 := binaryRecover maximum la mbc (ys 8) (ys 1) (ys 6) ![a,b,c] (hq 8) (hq 1) (hq 6)
  have h9 := binaryRecover maximum lb mac (ys 9) (ys 3) (ys 7) ![a,b,c] (hq 9) (hq 3) (hq 7)
  exact ⟨reconstructPair a (ys 0) (ys 1) h0 h1,reconstructPair b (ys 2) (ys 3) h2 h3,
    reconstructPair c (ys 4) (ys 5) h4 h5,h6,h7,h8,h9⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.MergeInterchangeQueriesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.MergeInterchangeQueriesProof
