module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.BinaryQueriesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.NumberedValueProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.NumberedQueriesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (suc)
open Continuation20261115 OriginalBoundsRecombination OriginalCodeBoundsRecursion OriginalRawSyntaxTransport
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

def source (n : Nat) (i : Fin 8) : Program 3 :=
  .composition (BinaryQueriesProof.queries n false i) ![.projection 1,.projection 2]
def size (n : Nat) : Program 3 := .composition (BinaryQueriesProof.totalSize n) ![.projection 1,.projection 2]
def label (n : Nat) : Program 3 := .composition maximum ![.projection 0,source n 6]
def result (n : Nat) : Program 3 := pairOf (succOf (size n)) (label n)
def queries (n : Nat) : Fin 10 → Program 3 :=
  ![source n 0,source n 1,source n 2,source n 3,source n 4,source n 5,source n 6,source n 7,label n,result n]

theorem recover (n : Nat) (k l r : OTerm alpha) (ys : Fin 10 → OTerm alpha)
    (hq : ∀ i, Nonempty (Derivation body Delta (programGraph (queries n i) (ys i) ![k,l,r]))) :
    Nonempty (Derivation body Delta (graph1 (bounds n) (ys 0) l)) ∧
    Nonempty (Derivation body Delta (graph2 InternalPairing.pairing (ys 0) (ys 1) (ys 2))) ∧
    Nonempty (Derivation body Delta (graph1 (bounds n) (ys 3) r)) ∧
    Nonempty (Derivation body Delta (graph2 InternalPairing.pairing (ys 3) (ys 4) (ys 5))) ∧
    Nonempty (Derivation body Delta (graph2 maximum (ys 6) (ys 2) (ys 5))) ∧
    Nonempty (Derivation body Delta (graph2 maximum (ys 8) k (ys 6))) ∧
    Nonempty (Derivation body Delta (graph2 InternalPairing.pairing (ys 9)
      (suc (OrdinaryArithmetic.addTerm (ys 1) (ys 4))) (ys 8))) := by
  let zs : Fin 8 → OTerm alpha := ![ys 0,ys 1,ys 2,ys 3,ys 4,ys 5,ys 6,ys 7]
  have hs : ∀ i, Nonempty (Derivation body Delta (graph2 (BinaryQueriesProof.queries n false i) (zs i) l r)) := by
    intro i
    fin_cases i
    · exact binaryRecover (BinaryQueriesProof.queries n false 0) (.projection 1) (.projection 2)
        (ys 0) l r ![k,l,r] (hq 0) (projectionValue 1 ![k,l,r]) (projectionValue 2 ![k,l,r])
    · exact binaryRecover (BinaryQueriesProof.queries n false 1) (.projection 1) (.projection 2)
        (ys 1) l r ![k,l,r] (hq 1) (projectionValue 1 ![k,l,r]) (projectionValue 2 ![k,l,r])
    · exact binaryRecover (BinaryQueriesProof.queries n false 2) (.projection 1) (.projection 2)
        (ys 2) l r ![k,l,r] (hq 2) (projectionValue 1 ![k,l,r]) (projectionValue 2 ![k,l,r])
    · exact binaryRecover (BinaryQueriesProof.queries n false 3) (.projection 1) (.projection 2)
        (ys 3) l r ![k,l,r] (hq 3) (projectionValue 1 ![k,l,r]) (projectionValue 2 ![k,l,r])
    · exact binaryRecover (BinaryQueriesProof.queries n false 4) (.projection 1) (.projection 2)
        (ys 4) l r ![k,l,r] (hq 4) (projectionValue 1 ![k,l,r]) (projectionValue 2 ![k,l,r])
    · exact binaryRecover (BinaryQueriesProof.queries n false 5) (.projection 1) (.projection 2)
        (ys 5) l r ![k,l,r] (hq 5) (projectionValue 1 ![k,l,r]) (projectionValue 2 ![k,l,r])
    · exact binaryRecover (BinaryQueriesProof.queries n false 6) (.projection 1) (.projection 2)
        (ys 6) l r ![k,l,r] (hq 6) (projectionValue 1 ![k,l,r]) (projectionValue 2 ![k,l,r])
    · exact binaryRecover (BinaryQueriesProof.queries n false 7) (.projection 1) (.projection 2)
        (ys 7) l r ![k,l,r] (hq 7) (projectionValue 1 ![k,l,r]) (projectionValue 2 ![k,l,r])
  obtain ⟨hl,hp,hr,hq',hm,_⟩ := BinaryQueriesProof.recover n false l r zs hs
  have hmax := binaryRecover maximum (.projection 0) (source n 6) (ys 8) k (ys 6) ![k,l,r]
    (hq 8) (projectionValue 0 ![k,l,r]) (hq 6)
  have ha : Nonempty (Derivation body Delta (graph2 (BinaryQueriesProof.totalSize n)
      (OrdinaryArithmetic.addTerm (ys 1) (ys 4)) l r)) :=
    binaryValue InternalArithmeticPrograms.addition (leftOf (BinaryQueriesProof.left n)) (leftOf (BinaryQueriesProof.right n))
      (OrdinaryArithmetic.addTerm (ys 1) (ys 4)) (ys 1) (ys 4) ![l,r]
      (InternalArithmeticProgramsSupportProof.additionValue (ys 1) (ys 4)) (hs 1) (hs 4)
  have hv : Nonempty (Derivation body Delta (graph3 (size n) (OrdinaryArithmetic.addTerm (ys 1) (ys 4)) k l r)) :=
    binaryValue (BinaryQueriesProof.totalSize n) (.projection 1) (.projection 2)
      (OrdinaryArithmetic.addTerm (ys 1) (ys 4)) l r ![k,l,r] ha (projectionValue 1 ![k,l,r]) (projectionValue 2 ![k,l,r])
  have hsucc := unaryValue .succ (size n) (suc (OrdinaryArithmetic.addTerm (ys 1) (ys 4)))
    (OrdinaryArithmetic.addTerm (ys 1) (ys 4)) ![k,l,r] (successorValue ![OrdinaryArithmetic.addTerm (ys 1) (ys 4)]) hv
  have ho := binaryRecover InternalPairing.pairing (succOf (size n)) (label n) (ys 9)
    (suc (OrdinaryArithmetic.addTerm (ys 1) (ys 4))) (ys 8) ![k,l,r] (hq 9) hsucc (hq 8)
  exact ⟨hl,hp,hr,hq',hm,hmax,ho⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.NumberedQueriesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.NumberedQueriesProof
