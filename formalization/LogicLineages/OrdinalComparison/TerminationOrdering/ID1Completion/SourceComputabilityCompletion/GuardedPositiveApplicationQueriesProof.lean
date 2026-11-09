module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.GuardedPositiveApplicationArithmeticProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.GuardedPositiveApplicationQueriesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof (andIntro)
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (OTerm suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

def markAt (measure : Program 1) (i : Fin 2) : Program 2 :=
  .composition measure (fun _ : Fin 1 => .projection i)

def nextAt (measure : Program 1) (i : Fin 2) : Program 2 :=
  pairOf (leftOf (markAt measure i))
    (.composition .succ (fun _ : Fin 1 => rightOf (markAt measure i)))

/-- These are ordinary original Program queries. In particular each new
mark is the literal pair of the old flag and successor old depth. -/
def queries (measure : Program 1) : Fin 8 → Program 2 :=
  Fin.cons (markAt measure 0) (Fin.cons (markAt measure 1)
    (Fin.cons (leftOf (markAt measure 0)) (Fin.cons (rightOf (markAt measure 0))
      (Fin.cons (leftOf (markAt measure 1)) (Fin.cons (rightOf (markAt measure 1))
        (Fin.cons (nextAt measure 0) (Fin.cons (nextAt measure 1) Fin.elim0)))))))

def facts {α : Type} (measure : Program 1) (f g : OTerm α) (ys : Fin 8 → OTerm α) : Formula α :=
  graph1 measure (ys 0) f ⊓ (graph1 measure (ys 1) g ⊓
    (graph1 InternalUnpair.left (ys 2) (ys 0) ⊓
      (graph1 InternalUnpair.right (ys 3) (ys 0) ⊓
        (graph1 InternalUnpair.left (ys 4) (ys 1) ⊓
          (graph1 InternalUnpair.right (ys 5) (ys 1) ⊓
            (graph2 InternalPairing.pairing (ys 6) (ys 2) (suc (ys 3)) ⊓
              graph2 InternalPairing.pairing (ys 7) (ys 4) (suc (ys 5))))))))

theorem queryFacts {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}
    (measure : Program 1) (f g : OTerm α) (ys : Fin 8 → OTerm α)
    (hq : ∀ i, Nonempty (Derivation body Gamma
      (programGraph (queries measure i) (ys i) (Fin.cons f (Fin.cons g Fin.elim0))))) :
    Nonempty (Derivation body Gamma (facts measure f g ys)) := by
  let xs : Fin 2 → OTerm α := Fin.cons f (Fin.cons g Fin.elim0)
  have hm0 := unaryRecover measure (.projection (0 : Fin 2)) (ys 0) f xs
    (hq 0) (projectionValue 0 xs)
  have hm1 := unaryRecover measure (.projection (1 : Fin 2)) (ys 1) g xs
    (hq 1) (projectionValue 1 xs)
  have hf0 := unaryRecover InternalUnpair.left (markAt measure 0) (ys 2) (ys 0) xs (hq 2) (hq 0)
  have hd0 := unaryRecover InternalUnpair.right (markAt measure 0) (ys 3) (ys 0) xs (hq 3) (hq 0)
  have hf1 := unaryRecover InternalUnpair.left (markAt measure 1) (ys 4) (ys 1) xs (hq 4) (hq 1)
  have hd1 := unaryRecover InternalUnpair.right (markAt measure 1) (ys 5) (ys 1) xs (hq 5) (hq 1)
  have hs0 := unaryValue .succ (rightOf (markAt measure 0)) (suc (ys 3)) (ys 3) xs
    (successorValue (Fin.cons (ys 3) Fin.elim0)) (hq 3)
  have hs1 := unaryValue .succ (rightOf (markAt measure 1)) (suc (ys 5)) (ys 5) xs
    (successorValue (Fin.cons (ys 5) Fin.elim0)) (hq 5)
  have hp0 := binaryRecover InternalPairing.pairing (leftOf (markAt measure 0))
    (.composition .succ (fun _ : Fin 1 => rightOf (markAt measure 0)))
    (ys 6) (ys 2) (suc (ys 3)) xs (hq 6) (hq 2) hs0
  have hp1 := binaryRecover InternalPairing.pairing (leftOf (markAt measure 1))
    (.composition .succ (fun _ : Fin 1 => rightOf (markAt measure 1)))
    (ys 7) (ys 4) (suc (ys 5)) xs (hq 7) (hq 4) hs1
  exact andIntro hm0 (andIntro hm1 (andIntro hf0 (andIntro hd0
    (andIntro hf1 (andIntro hd1 (andIntro hp0 hp1))))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.GuardedPositiveApplicationQueriesProof
