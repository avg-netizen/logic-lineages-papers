module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.DeletionChainTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorErasureProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.DeletionChainProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open SixSol20261113.Erasure
open EvaluatorErasureDefinitions DeletionChainDefinitions
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem step (R : Program 2) (H G : Program 1) (M W : Program 2)
    (left right nextLeft nextRight parameter nextParameter c gamma nextGamma count cutoff selectedType : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (AdmittedPair R H G M W left right parameter)))
    (ht : Nonempty (Derivation body Delta (Transition left right nextLeft nextRight parameter nextParameter c gamma nextGamma count cutoff selectedType))) :
    Nonempty (Derivation body Delta (AdmittedPair R H G M W nextLeft nextRight nextParameter)) :=
  EvaluatorErasureProof.actualErasureCongruence R H G M W body alpha Delta
    left right nextLeft nextRight parameter nextParameter c gamma nextGamma count cutoff selectedType ha
    (andLeft ht) (andLeft (andRight ht)) (andLeft (andRight (andRight ht)))
    (andLeft (andRight (andRight (andRight ht))))
    (andLeft (andRight (andRight (andRight (andRight ht)))))
    (andLeft (andRight (andRight (andRight (andRight (andRight ht))))))
    (andLeft (andRight (andRight (andRight (andRight (andRight (andRight ht)))))))
    (andRight (andRight (andRight (andRight (andRight (andRight (andRight ht)))))))

theorem actual : DeletionChainTargets.ActualFiniteChain := by
  intro R H G M W body alpha Delta steps
  induction steps with
  | zero =>
    intro left right parameter gamma count cutoff selectedType c ha ht
    exact ha
  | succ steps ih =>
    intro left right parameter gamma count cutoff selectedType c ha ht
    have hprefix := ih
      (fun i => left i.castSucc) (fun i => right i.castSucc)
      (fun i => parameter i.castSucc) (fun i => gamma i.castSucc)
      (fun i => count i.castSucc) (fun i => cutoff i.castSucc) (fun i => selectedType i.castSucc) c ha
      (fun i => ht i.castSucc)
    exact step R H G M W
      (left (Fin.last steps).castSucc) (right (Fin.last steps).castSucc)
      (left (Fin.last steps).succ) (right (Fin.last steps).succ)
      (parameter (Fin.last steps).castSucc) (parameter (Fin.last steps).succ) c
      (gamma (Fin.last steps).castSucc) (gamma (Fin.last steps).succ)
      (count (Fin.last steps)) (cutoff (Fin.last steps)) (selectedType (Fin.last steps))
      hprefix (ht (Fin.last steps))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.DeletionChainProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.DeletionChainProof
