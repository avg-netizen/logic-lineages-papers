module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.BinaryValueProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.BinaryQueriesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (suc)
open Continuation20261115 OriginalCodeBoundsRecursion OriginalBoundsRecombination OriginalRawSyntaxTransport
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

def left (n : Nat) : Program 2 := .composition (bounds n) (fun _ : Fin 1 => .projection (0 : Fin 2))
def right (n : Nat) : Program 2 := .composition (bounds n) (fun _ : Fin 1 => .projection (1 : Fin 2))
def totalSize (n : Nat) : Program 2 := addOf (leftOf (left n)) (leftOf (right n))
def label (n : Nat) : Program 2 := .composition maximum ![rightOf (left n),rightOf (right n)]
def result (n : Nat) (cons : Bool) : Program 2 := pairOf (if cons then totalSize n else succOf (totalSize n)) (label n)
def queries (n : Nat) (cons : Bool) : Fin 8 → Program 2 :=
  ![left n,leftOf (left n),rightOf (left n),right n,leftOf (right n),rightOf (right n),label n,result n cons]

theorem recover (n : Nat) (cons : Bool) (l r : OTerm alpha) (ys : Fin 8 → OTerm alpha)
    (hq : ∀ i, Nonempty (Derivation body Delta (programGraph (queries n cons i) (ys i) ![l,r]))) :
    Nonempty (Derivation body Delta (graph1 (bounds n) (ys 0) l)) ∧
    Nonempty (Derivation body Delta (graph2 InternalPairing.pairing (ys 0) (ys 1) (ys 2))) ∧
    Nonempty (Derivation body Delta (graph1 (bounds n) (ys 3) r)) ∧
    Nonempty (Derivation body Delta (graph2 InternalPairing.pairing (ys 3) (ys 4) (ys 5))) ∧
    Nonempty (Derivation body Delta (graph2 maximum (ys 6) (ys 2) (ys 5))) ∧
    Nonempty (Derivation body Delta (graph2 InternalPairing.pairing (ys 7)
      (if cons then OrdinaryArithmetic.addTerm (ys 1) (ys 4) else suc (OrdinaryArithmetic.addTerm (ys 1) (ys 4))) (ys 6))) := by
  have hl := unaryRecover (bounds n) (.projection 0) (ys 0) l ![l,r] (hq 0) (projectionValue 0 ![l,r])
  have hr := unaryRecover (bounds n) (.projection 1) (ys 3) r ![l,r] (hq 3) (projectionValue 1 ![l,r])
  have hls := unaryRecover InternalUnpair.left (left n) (ys 1) (ys 0) ![l,r] (hq 1) (hq 0)
  have hll := unaryRecover InternalUnpair.right (left n) (ys 2) (ys 0) ![l,r] (hq 2) (hq 0)
  have hrs := unaryRecover InternalUnpair.left (right n) (ys 4) (ys 3) ![l,r] (hq 4) (hq 3)
  have hrl := unaryRecover InternalUnpair.right (right n) (ys 5) (ys 3) ![l,r] (hq 5) (hq 3)
  have hp := reconstructPair (ys 0) (ys 1) (ys 2) hls hll
  have hq' := reconstructPair (ys 3) (ys 4) (ys 5) hrs hrl
  have hm := binaryRecover maximum (rightOf (left n)) (rightOf (right n)) (ys 6) (ys 2) (ys 5) ![l,r] (hq 6) (hq 2) (hq 5)
  have ha : Nonempty (Derivation body Delta (graph2 (totalSize n) (OrdinaryArithmetic.addTerm (ys 1) (ys 4)) l r)) :=
    binaryValue InternalArithmeticPrograms.addition (leftOf (left n)) (leftOf (right n))
      (OrdinaryArithmetic.addTerm (ys 1) (ys 4)) (ys 1) (ys 4) ![l,r]
      (InternalArithmeticProgramsSupportProof.additionValue (ys 1) (ys 4)) (hq 1) (hq 4)
  have ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing (ys 7)
      (if cons then OrdinaryArithmetic.addTerm (ys 1) (ys 4) else suc (OrdinaryArithmetic.addTerm (ys 1) (ys 4))) (ys 6))) := by
    cases cons
    · have hs := unaryValue .succ (totalSize n) (suc (OrdinaryArithmetic.addTerm (ys 1) (ys 4)))
        (OrdinaryArithmetic.addTerm (ys 1) (ys 4)) ![l,r]
        (successorValue ![OrdinaryArithmetic.addTerm (ys 1) (ys 4)]) ha
      exact binaryRecover InternalPairing.pairing (succOf (totalSize n)) (label n) (ys 7)
        (suc (OrdinaryArithmetic.addTerm (ys 1) (ys 4))) (ys 6) ![l,r] (hq 7) hs (hq 6)
    · exact binaryRecover InternalPairing.pairing (totalSize n) (label n) (ys 7)
        (OrdinaryArithmetic.addTerm (ys 1) (ys 4)) (ys 6) ![l,r] (hq 7) ha (hq 6)
  exact ⟨hl,hp,hr,hq',hm,ho⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.BinaryQueriesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.BinaryQueriesProof
