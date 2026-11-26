module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.UnaryBoundsCongruenceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.BinaryQueriesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.BinaryBoundsCongruenceProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261115.OriginalBoundsRecombination (maximum merge)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalTagArithmeticSyntaxProof (z suc eqn sucRelabel zRelabel eqnRelabel)
open InternalTagArithmeticSupportProof (trans symm)
open Continuation20261115
open OriginalCodeBoundsConstructors.BinaryRootProof (constructor)

theorem sameChildValues (cons : Bool) (n : Nat)
    (left right lm rm lc ld rc rd first second lv rv : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (graph3 (constructor cons) left lm lc ld)))
    (hrc : Nonempty (Derivation body Delta (graph3 (constructor cons) right rm rc rd)))
    (hlg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) left)))
    (hrg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) right)))
    (hlfirst : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) first lc)))
    (hrfirst : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) first rc)))
    (hlsecond : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) second ld)))
    (hrsecond : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) second rd)))
    (hlv : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) lv left)))
    (hrv : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) rv right)))
    : Nonempty (Derivation body Delta (eqn lv rv)) := by
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases (OriginalCodeBoundsConstructors.BinaryQueriesProof.queries n cons) ![lc,ld] _
  intro beta j ys Theta hj hq
  have hx : (fun i => (![lc,ld] i).relabel j) = ![lc.relabel j,ld.relabel j] := by
    funext i; fin_cases i <;> rfl
  rw [hx] at hq
  rw [eqnRelabel]
  obtain ⟨hc1,hp1,hc2,hp2,hm,ho⟩ := OriginalCodeBoundsConstructors.BinaryQueriesProof.recover n cons (lc.relabel j) (ld.relabel j) ys hq
  have hlcj := renameInto hlc j Theta hj
  have hrcj := renameInto hrc j Theta hj
  have hlgj := renameInto hlg j Theta hj
  have hrgj := renameInto hrg j Theta hj
  have hlfirstj := renameInto hlfirst j Theta hj
  have hrfirstj := renameInto hrfirst j Theta hj
  have hlsecondj := renameInto hlsecond j Theta hj
  have hrsecondj := renameInto hrsecond j Theta hj
  have hlvj := renameInto hlv j Theta hj
  have hrvj := renameInto hrv j Theta hj
  rw [graph3Rename] at hlcj hrcj
  simp only [graph1Rename,sucRelabel,zRelabel] at hlgj hrgj hlfirstj hrfirstj hlsecondj hrsecondj hlvj hrvj
  have he1 := valueUnique (OriginalCodeBoundsRecursion.bounds n) (first.relabel j) (ys 0) ![lc.relabel j] hlfirstj hc1
  have he2 := valueUnique (OriginalCodeBoundsRecursion.bounds n) (second.relabel j) (ys 3) ![ld.relabel j] hlsecondj hc2
  have hr1 := outputTransport (OriginalCodeBoundsRecursion.bounds n) (first.relabel j) (ys 0) ![rc.relabel j] he1 hrfirstj
  have hr2 := outputTransport (OriginalCodeBoundsRecursion.bounds n) (second.relabel j) (ys 3) ![rd.relabel j] he2 hrsecondj
  have hl := OriginalCodeBoundsConstructors.BinaryValueProof.value cons n (left.relabel j) (lm.relabel j) (lc.relabel j) (ld.relabel j)
    (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) (ys 6) (ys 7) hlcj hlgj hc1 hc2 hp1 hp2 hm ho
  have hr := OriginalCodeBoundsConstructors.BinaryValueProof.value cons n (right.relabel j) (rm.relabel j) (rc.relabel j) (rd.relabel j)
    (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) (ys 6) (ys 7) hrcj hrgj hr1 hr2 hp1 hp2 hm ho
  obtain ⟨hel⟩ := valueUnique (OriginalCodeBoundsRecursion.bounds n) (lv.relabel j) (ys 7) ![left.relabel j] hlvj hl
  obtain ⟨her⟩ := valueUnique (OriginalCodeBoundsRecursion.bounds n) (rv.relabel j) (ys 7) ![right.relabel j] hrvj hr
  exact ⟨trans hel (symm her)⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.BinaryBoundsCongruenceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.BinaryBoundsCongruenceProof
