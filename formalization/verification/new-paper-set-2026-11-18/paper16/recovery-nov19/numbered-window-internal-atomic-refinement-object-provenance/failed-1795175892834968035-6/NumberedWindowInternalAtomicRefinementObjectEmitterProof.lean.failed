module
public import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchControlChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairGraphProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFixedWindowVertexDispatchSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalControlGraphSupportProof
  (compositionValue projectionValue valueUnique outputTransport equalEqn)
open ID1Completion.InternalTagArithmeticSyntaxProof (z eqn)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open ID1Completion.InternalFixedWindowVertexDispatchSupportProof (constantValue)
open ID1Completion.InternalGraphCompositionEqualityProof (graphInputTransport)
open NumberedWindowInternalProbeTargets (OTerm)
open NumberedWindowInternalFreshProbeEmitter (consOf)
open NumberedWindowInternalFreshProbeEmitterObjectTargets (consTerm)
open NumberedWindowInternalFreshProbeDispatchProgram (zeroAt literal)
open NumberedWindowInternalFreshProbeDispatchControlChecks (exact_DispatchControlAST)
open NumberedWindowInternalSparsePair (fieldCons)
open NumberedWindowInternalSparsePairGraphProof (consGraph)
open NumberedWindowInternalAtomicRefinement NumberedWindowInternalAtomicRefinementObjectTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem literalGraph {m : Nat} (k : Nat) (xs : Fin m → OTerm α) :
    Nonempty (Derivation body Γ (programGraph (literal m k) (numeral k) xs)) := by
  rw [exact_DispatchControlAST.2.1]
  exact constantValue m k xs

theorem unaryInput (p : Program 1) (out src dst : OTerm α)
    (e : Nonempty (Derivation body Γ (equal src dst)))
    (h : Nonempty (Derivation body Γ (programGraph p out ![src]))) :
    Nonempty (Derivation body Γ (programGraph p out ![dst])) := by
  apply graphInputTransport body α 1 Γ (OrdinaryArithmetic.graphFormula p) out ![src] ![dst] _ h
  intro i
  obtain rfl := Fin.eq_zero i
  exact e

private theorem consOfGraph {n : Nat} (p q : Program n) (x y : OTerm α)
    (xs : Fin n → OTerm α)
    (hp : Nonempty (Derivation body Γ (programGraph p x xs)))
    (hq : Nonempty (Derivation body Γ (programGraph q y xs))) :
    Nonempty (Derivation body Γ (programGraph (consOf p q) (consTerm x y) xs)) := by
  unfold consOf
  apply compositionValue fieldCons (Fin.cons p (Fin.cons q Fin.elim0))
    (consTerm x y) xs ![x,y] (consGraph x y)
  intro i
  exact Fin.cases hp (Fin.cases hq (fun k => Fin.elim0 k)) i

theorem bottomEmitterGraph (c t : OTerm α) :
    Nonempty (Derivation body Γ (programGraph bottomEmitter (packedBottomTerm c t) ![c,t])) := by
  let xs : Fin 2 → OTerm α := ![c,t]
  let pc : Program 2 := .projection 0
  let pt : Program 2 := .projection 1
  let pg : Program 2 := literal 2 3
  let pz : Program 2 := zeroAt 2
  have hc : Nonempty (Derivation body Γ (programGraph pc c xs)) := projectionValue 0 xs
  have ht : Nonempty (Derivation body Γ (programGraph pt t xs)) := projectionValue 1 xs
  have hg : Nonempty (Derivation body Γ (programGraph pg (numeral 3) xs)) := literalGraph 3 xs
  have hz : Nonempty (Derivation body Γ (programGraph pz z xs)) := literalGraph 0 xs
  let pp := consOf pg (consOf pt pz)
  let payload := consTerm (numeral 3) (consTerm t z)
  have hp := consOfGraph pg (consOf pt pz) (numeral 3) (consTerm t z) xs hg
    (consOfGraph pt pz t z xs ht hz)
  have tail := consOfGraph pp pz payload z xs hp hz
  have row := consOfGraph pt (consOf pp pz) t (consTerm payload z) xs ht tail
  have fields := consOfGraph pc (consOf pt (consOf pp pz)) c
    (consTerm t (consTerm payload z)) xs hc row
  exact consOfGraph pg (consOf pc (consOf pt (consOf pp pz))) (numeral 3)
    (consTerm c (consTerm t (consTerm payload z))) xs hg fields

theorem exactEmitter : ExactOpenAtomicBottomEmitter := by
  intro body α Γ out c t
  dsimp only
  let G := programGraph bottomEmitter out ![c,t]
  let E := eqn out (packedBottomTerm c t)
  rw [equalEqn]
  obtain ⟨hf⟩ := valueUnique (body := body) (Gamma := G :: Γ)
    bottomEmitter out (packedBottomTerm c t) ![c,t]
    ⟨Derivation.hypothesis List.mem_cons_self⟩ (bottomEmitterGraph c t)
  obtain ⟨hr⟩ := outputTransport (body := body) (Gamma := E :: Γ)
    bottomEmitter (packedBottomTerm c t) out ![c,t]
    ⟨symm (Derivation.hypothesis List.mem_cons_self)⟩ (bottomEmitterGraph c t)
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hr)⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
