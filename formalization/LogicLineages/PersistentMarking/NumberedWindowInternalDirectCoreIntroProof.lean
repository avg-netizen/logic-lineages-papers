module
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectWitnessEnvelopeOpenProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreIntroProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue equalEqn)
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept)
open ID1Completion.InternalTagArithmeticSupportProof (refl)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalDirectBoundaryGuardsTargets (boundaryRaw)
open NumberedWindowInternalDirectSourcePartitionRawTargets (sourceTape observePartition rawSourceCheck)
open NumberedWindowInternalDirectTargetPartitionRawTargets (rawTargetCheck)
open NumberedWindowInternalDirectInsertedScanTargets (scan)
open NumberedWindowInternalDirectWitnessEnvelopeTargets (reports guardAt tripleTerm)
open NumberedWindowInternalDirectWitnessEnvelope (exactOpenTriple)
open NumberedWindowInternalDirectCoreTargets

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem routeIntro {n : Nat} (p : Program n) (indices : Fin n → Fin 5)
    (xs : Fin 5 → OTerm α)
    (h : Nonempty (Derivation B Γ (programGraph p (suc z) (fun i => xs (indices i))))) :
    Nonempty (Derivation B Γ (programGraph (route p indices) (suc z) xs)) :=
  compositionValue p (fun i => .projection (indices i)) (suc z) xs (fun i => xs (indices i))
    h (fun i => projectionValue (indices i) xs)

/-- Combine the four actual reports with the original ordered projections
and original nested conjunction. This rebuilds the same physical core. -/
theorem exact_OriginalCoreFromCut (i : Program 1) (r : Program 3) (count : Program 2)
    (s t k d a : OTerm α) (p : Cut i r count B Γ s t k d a) :
    Nonempty (Derivation B Γ (programGraph (core i r count) (suc z) (coreTape s t k d a))) := by
  let xs := coreTape s t k d a
  have read3 (x y z : Fin 5) : (fun l : Fin 3 => xs (![x,y,z] l)) = ![xs x,xs y,xs z] := by
    funext l
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun q => Fin.elim0 q))) l
  have read2 (x y : Fin 5) : (fun l : Fin 2 => xs (![x,y] l)) = ![xs x,xs y] := by
    funext l
    exact Fin.cases rfl (Fin.cases rfl (fun q => Fin.elim0 q)) l
  have b : Nonempty (Derivation B Γ (programGraph (boundaryAt i) (suc z) xs)) :=
    routeIntro (boundaryRaw i) ![0,1,3] xs (by rw [read3]; exact p.scalarBoundary)
  have f : Nonempty (Derivation B Γ (programGraph (sourceAt count) (suc z) xs)) :=
    routeIntro (rawSourceCheck (observePartition count)) ![0,2,3] xs (by rw [read3]; exact p.sourceObserver)
  have g : Nonempty (Derivation B Γ (programGraph (targetAt count) (suc z) xs)) :=
    routeIntro (rawTargetCheck count) ![1,2,4] xs (by rw [read3]; exact p.targetObserver)
  have h : Nonempty (Derivation B Γ (programGraph (scanAt r) (suc z) xs)) :=
    routeIntro (scan r) ![4,3] xs (by rw [read2]; exact p.insertionScan)
  let right := conjunction (targetAt count) (scanAt r)
  exact conjunctionAccept (boundaryAt i) (conjunction (sourceAt count) right) xs b
    (conjunctionAccept (sourceAt count) right xs f (conjunctionAccept (targetAt count) (scanAt r) xs g h))

private theorem atCert (p : Program 1) (s w t out : OTerm α)
    (value : Nonempty (Derivation B Γ (unary p out w))) :
    Nonempty (Derivation B Γ (programGraph (onCert p) out (sourceTape s w t))) := by
  apply compositionValue p ![.projection 1] out (sourceTape s w t) ![w] value
  intro j
  obtain rfl := Fin.eq_zero j
  exact projectionValue 1 (sourceTape s w t)

/-- The actual selected dCore accepts the genuine tag-5 packed witness
with the supplied exact checked fields. Source and target are unchanged
raw terms; there is no numeric calibration premise. -/
theorem exact_OriginalDCoreFromCut (i : Program 1) (r : Program 3) (count : Program 2)
    (s t k d a : OTerm α) (p : Cut i r count B Γ s t k d a) :
    Nonempty (Derivation B Γ (programGraph (dCore i r count) (suc z)
      (sourceTape s (tripleTerm 5 k d a) t))) := by
  let w := tripleTerm 5 k d a
  let tape := sourceTape s w t
  obtain ⟨both⟩ := exactOpenTriple B α Γ 5 w k d a
  have eq : Nonempty (Derivation B Γ (equal w (tripleTerm 5 k d a))) := by
    rw [equalEqn]
    exact ⟨refl w⟩
  obtain ⟨e⟩ := eq
  have fields : Derivation B Γ (reports 5 w k d a) :=
    Derivation.implicationElimination (Derivation.conjunctionLeft both) e
  have f := Derivation.conjunctionRight fields
  have g := Derivation.conjunctionRight f
  have guard := atCert (guardAt 5) s w t (suc z) ⟨Derivation.conjunctionLeft fields⟩
  have k' := atCert (field 0) s w t k ⟨Derivation.conjunctionLeft f⟩
  have d' := atCert (field 1) s w t d ⟨Derivation.conjunctionLeft g⟩
  have a' := atCert (field 2) s w t a ⟨Derivation.conjunctionRight g⟩
  have comp : Nonempty (Derivation B Γ (programGraph (.composition (core i r count) witnessAt) (suc z) tape)) := by
    apply compositionValue (core i r count) witnessAt (suc z) tape (coreTape s t k d a)
      (exact_OriginalCoreFromCut i r count s t k d a p)
    intro j
    exact Fin.cases (projectionValue 0 tape) (Fin.cases (projectionValue 2 tape)
      (Fin.cases k' (Fin.cases d' (Fin.cases a' (fun u => Fin.elim0 u))))) j
  exact conjunctionAccept (onCert (guardAt 5)) (.composition (core i r count) witnessAt) tape guard comp

#print axioms exact_OriginalCoreFromCut
#print axioms exact_OriginalDCoreFromCut
end LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreIntroProof
