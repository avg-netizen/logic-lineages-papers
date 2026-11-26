module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.PointSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedBooleanRange.PayloadProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadWindowBooleanRange.ProgramRangeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.PointBindingProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb)
open Continuation20261114.HeadWindowBooleanRange
open Continuation20261114.HeadWindowBooleanRange.InductionSyntaxProof (booleanRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open PointRange PointSyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)} {k : Nat}
attribute [local irreducible] programGraph

theorem introAt (p : Program k) (xs : Fin k → OTerm alpha)
    (h : Nonempty (Derivation body (Delta.map (fun q => q.relabel Sum.inl)) (PointRange.matrix p xs))) :
    Nonempty (Derivation body Delta (At p xs)) :=
  InternalClosedProgramsBindingProof.introduction body alpha 1 Delta _ h

theorem applyAt (p : Program k) (xs : Fin k → OTerm alpha) (out : OTerm alpha)
    (h : Nonempty (Derivation body Delta (At p xs)))
    (hg : Nonempty (Derivation body Delta (programGraph p out xs))) :
    Nonempty (Derivation body Delta (BooleanValue out)) := by
  obtain ⟨h⟩ := InternalClosedProgramsBindingProof.elimination body alpha 1 Delta
    (PointRange.matrix p xs) (fun _ => emb out) h
  rw [matrixWitness] at h
  obtain ⟨hg⟩ := hg
  exact ⟨Derivation.implicationElimination h hg⟩

theorem fromRange (p : Program k) (xs : Fin k → OTerm alpha) (hr : ProgramRangeProof.Ranged p) :
    Nonempty (Derivation body Delta (At p xs)) := by
  apply introAt p xs
  apply Nonempty.intro
  apply Derivation.implicationIntroduction
  exact Classical.choice (hr body (alpha ⊕ Fin 1) _ (.var (.inr 0)) (fun i => (xs i).relabel Sum.inl)
    ⟨Derivation.hypothesis List.mem_cons_self⟩)

theorem fromValue (p : Program k) (xs : Fin k → OTerm alpha) (value : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph p value xs)))
    (hb : Nonempty (Derivation body Delta (BooleanValue value))) :
    Nonempty (Derivation body Delta (At p xs)) := by
  apply introAt p xs
  apply Nonempty.intro
  apply Derivation.implicationIntroduction
  let Theta : List (Formula (alpha ⊕ Fin 1)) :=
    programGraph p (.var (.inr 0)) (fun i => (xs i).relabel Sum.inl) :: Delta.map (fun q => q.relabel Sum.inl)
  have hj : ∀ q ∈ Delta, q.relabel (Sum.inl : alpha → alpha ⊕ Fin 1) ∈ Theta := by
    intro q hq
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩)
  have hpj := renameInto hp (Sum.inl : alpha → alpha ⊕ Fin 1) Theta hj
  rw [programRename] at hpj
  have hbj := renameInto hb (Sum.inl : alpha → alpha ⊕ Fin 1) Theta hj
  rw [booleanRename] at hbj
  have hg : Nonempty (Derivation body Theta (programGraph p (.var (.inr 0)) (fun i => (xs i).relabel Sum.inl))) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have he := valueUnique p (.var (.inr 0)) (value.relabel Sum.inl) (fun i => (xs i).relabel Sum.inl) hg hpj
  exact Classical.choice (Continuation20261115.OriginalDecodedBooleanRange.PayloadProof.transport _ _ he hbj)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.PointBindingProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.PointBindingProof
