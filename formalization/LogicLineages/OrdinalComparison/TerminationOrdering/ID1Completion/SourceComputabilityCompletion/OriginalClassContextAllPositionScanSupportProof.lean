module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextAllPositionObserverTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalPairingOrderArithmeticProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextAllPositionScanSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceConjunctionProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof (symm)
open InternalApplicationStepPeelSupportProof (andLeft andRight andIntro)
open OriginalClassContextAllPositionObserver
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Acceptance of an actual recursion successor exposes both the previous
acceptance and the test at the actual final index. -/
theorem atPrevious (R : Program 2) (count previous seed candidate parameter : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph4 (scan R) previous count seed candidate parameter)))
    (hs : Nonempty (Derivation body Delta (graph4 (scan R) (suc z) (suc count) seed candidate parameter))) :
    Nonempty (Derivation body Delta
      (graph4 (scan R) (suc z) count seed candidate parameter ⊓
       graph4 (positionTest R) (suc z) count seed candidate parameter)) := by
  let params : Fin 3 → OTerm alpha := Fin.cons seed (Fin.cons candidate (Fin.cons parameter Fin.elim0))
  let xs : Fin 5 → OTerm alpha := Fin.cons count (Fin.cons previous params)
  let g : Fin 4 → Program 5 := ![.projection 0,.projection 2,.projection 3,.projection 4]
  have ht := InternalRawListRecursionSupportProof.recursionRecover
    (InternalLessThan.constantOne 3) (scanStep R) (suc z) previous count params hp hs
  have hc := conjunctionRecover (.projection (1 : Fin 5)) (.composition (positionTest R) g) xs ht
  have he := valueUnique (.projection (1 : Fin 5)) (suc z) previous xs
    (andLeft hc) (projectionValue 1 xs)
  obtain ⟨he⟩ := he
  have hprev := outputTransport (scan R) previous (suc z) (Fin.cons count params) ⟨symm he⟩ hp
  have htest := compositionRecover (positionTest R) g (suc z) xs (Fin.cons count params) (andRight hc)
    (fun i => Fin.cases (projectionValue 0 xs)
      (Fin.cases (projectionValue 2 xs)
        (Fin.cases (projectionValue 3 xs)
          (Fin.cases (projectionValue 4 xs) (fun k => Fin.elim0 k)))) i)
  exact andIntro hprev htest

theorem successorExposure (R : Program 2) (count seed candidate parameter : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph4 (scan R) (suc z) (suc count) seed candidate parameter))) :
    Nonempty (Derivation body Delta
      (graph4 (scan R) (suc z) count seed candidate parameter ⊓
       graph4 (positionTest R) (suc z) count seed candidate parameter)) := by
  let xs : Fin 4 → OTerm alpha := Fin.cons count (Fin.cons seed (Fin.cons candidate (Fin.cons parameter Fin.elim0)))
  apply programCases (scan R) xs _
  intro beta j Theta previous hj hp
  have hx : (fun i => (xs i).relabel j) =
      Fin.cons (count.relabel j) (Fin.cons (seed.relabel j)
        (Fin.cons (candidate.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0))) := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))) i
  rw [hx] at hp
  have hs' := renameInto hs j Theta hj
  simp only [graph4Rename,sucRelabel,zRelabel] at hs'
  simp only [conjunctionRename,graph4Rename,sucRelabel,zRelabel]
  exact atPrevious R (count.relabel j) previous (seed.relabel j) (candidate.relabel j) (parameter.relabel j) hp hs'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextAllPositionScanSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextAllPositionScanSupportProof
