module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseOpenRoundsTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseOpenRoundsRecursionProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseOpenRoundsChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalListCodec (consCode)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue recursionZeroValue)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparseDirectedFilter (pass passTape cell)
open NumberedWindowInternalSparseDirectedRounds
open NumberedWindowInternalSparseOpenRoundsTargets
open NumberedWindowInternalSparseOpenRoundsRecursionProof

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem seedValue (xs : Fin 4 → OTerm α) (s : OTerm α)
    (known : Nonempty (Derivation body Γ (cell s (xs 3) z))) :
    Nonempty (Derivation body Γ (programGraph singletonSeed s xs)) := by
  apply compositionValue consCode ![.projection 3,constantZero 4] s xs ![xs 3,z] known
  intro k
  refine Fin.cases ?_ (fun k => ?_) k
  · exact projectionValue 3 xs
  · obtain rfl := Fin.eq_zero k
    exact constantZeroValue xs

private theorem baseArgs (xs : Fin 4 → OTerm α) (s : OTerm α)
    (known : Nonempty (Derivation body Γ (cell s (xs 3) z))) (k : Fin 4) :
    Nonempty (Derivation body Γ (programGraph
      ((![.projection 0,singletonSeed,.projection 1,.projection 2] : Fin 4 → Program 4) k)
      (passTape (xs 0) s (xs 1) (xs 2) k) xs)) := by
  refine Fin.cases ?_ (fun a => Fin.cases ?_ (fun b => Fin.cases ?_ (fun c => ?_) b) a) k
  · exact projectionValue 0 xs
  · exact seedValue xs s known
  · exact projectionValue 1 xs
  · obtain rfl := Fin.eq_zero c
    exact projectionValue 2 xs

theorem exact_OpenRoundZero : ExactOpenRoundZero := by
  intro E body α Γ out vertices ctx ty seed s
  let xs := membersTape vertices ctx ty seed
  apply conditional
  · intro Δ known chosen
    have baseCall := zeroRead roundBase (roundStep E) out xs chosen
    exact compositionRecover (pass (constantZero 4)) _ out xs
      (passTape vertices s ctx ty) baseCall (baseArgs xs s known)
  · intro Δ known chosen
    apply recursionZeroValue roundBase (roundStep E) out xs
    exact compositionValue (pass (constantZero 4)) _ out xs
      (passTape vertices s ctx ty) chosen (baseArgs xs s known)

private theorem stepArgs (xs : Fin 6 → OTerm α) (k : Fin 4) :
    Nonempty (Derivation body Γ (programGraph
      ((![.projection 2,.projection 1,.projection 3,.projection 4] : Fin 4 → Program 6) k)
      (passTape (xs 2) (xs 1) (xs 3) (xs 4) k) xs)) := by
  refine Fin.cases ?_ (fun a => Fin.cases ?_ (fun b => Fin.cases ?_ (fun c => ?_) b) a) k
  · exact projectionValue 2 xs
  · exact projectionValue 1 xs
  · exact projectionValue 3 xs
  · obtain rfl := Fin.eq_zero c
    exact projectionValue 4 xs

theorem exact_OpenRoundSuccessor : ExactOpenRoundSuccessor := by
  intro E body α Γ out fuel vertices ctx ty seed previous
  let xs := membersTape vertices ctx ty seed
  let ys := Fin.cons fuel (Fin.cons previous xs)
  apply conditional
  · intro Δ before after
    have step := succRead roundBase (roundStep E) out fuel previous xs before after
    exact compositionRecover (pass E) _ out ys (passTape vertices previous ctx ty) step (stepArgs ys)
  · intro Δ before after
    apply succWrite roundBase (roundStep E) out fuel previous xs before
    exact compositionValue (pass E) _ out ys (passTape vertices previous ctx ty) after (stepArgs ys)

private theorem memberArgs (xs : Fin 4 → OTerm α) (fuel : OTerm α)
    (length : Nonempty (Derivation body Γ (unary poolLength fuel (xs 0)))) (k : Fin 5) :
    Nonempty (Derivation body Γ (programGraph
      ((![selectedFuel,.projection 0,.projection 1,.projection 2,.projection 3] : Fin 5 → Program 4) k)
      (roundsTape fuel (xs 0) (xs 1) (xs 2) (xs 3) k) xs)) := by
  refine Fin.cases ?_ (fun a => Fin.cases ?_ (fun b =>
    Fin.cases ?_ (fun c => Fin.cases ?_ (fun d => ?_) c) b) a) k
  · apply compositionValue poolLength (fun _ : Fin 1 => .projection 0) fuel xs ![xs 0] length
    intro i
    obtain rfl := Fin.eq_zero i
    exact projectionValue 0 xs
  · exact projectionValue 0 xs
  · exact projectionValue 1 xs
  · exact projectionValue 2 xs
  · obtain rfl := Fin.eq_zero d
    exact projectionValue 3 xs

theorem exact_OpenMembersAtLength : ExactOpenMembersAtLength := by
  intro E body α Γ out fuel vertices ctx ty seed
  let xs := membersTape vertices ctx ty seed
  let ys := roundsTape fuel vertices ctx ty seed
  apply conditional
  · intro Δ length chosen
    exact compositionRecover (rounds E) _ out xs ys chosen (memberArgs xs fuel length)
  · intro Δ length chosen
    exact compositionValue (rounds E) _ out xs ys chosen (memberArgs xs fuel length)

#print axioms exact_OpenRoundZero
#print axioms exact_OpenRoundSuccessor
#print axioms exact_OpenMembersAtLength
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseOpenRoundsChecks
