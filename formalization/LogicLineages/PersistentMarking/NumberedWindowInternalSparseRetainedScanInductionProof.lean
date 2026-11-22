module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRetainedScanTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRetainedScanSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRetainedScanStepProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionCompositionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedSeenOpenChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListInductionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRetainedScanInductionProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalListCodecSupportProof (consGraph)
open ID1Completion.InternalListInduction (atCode atIndex constructorBody constructors premises)
open ID1Completion.InternalListInductionProof (actualOriginalListInductionAtCode)
open ID1Completion.InternalClosedProgramsBindingProof (actualFiniteUniversalIntroduction)
open ID1Completion.InternalBetaTotalityProof (addHyp)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseDirectedFilter (passGraph)
open NumberedWindowInternalSparseDirectedSeen (scanGraph seenWitness)
open NumberedWindowInternalSparseDirectedSeenOpenChecks (exact_OpenDirectedSeenWitness)
open NumberedWindowInternalSparseRetainedScanTargets
open NumberedWindowInternalSparseFilterInclusionSyntaxProof (hitGraph)
open NumberedWindowInternalSparseFilterInclusionCompositionProof (hitIntro)
open NumberedWindowInternalSparseRetainedScanSyntaxProof
  (hitScan scanInvariant scanInvariantCode scanInvariantIndex)
open NumberedWindowInternalSparseRetainedScanStepProof (atNil atCons)

private theorem constructorDerivation (E : Program 4) (body : Positive (Fin 1)) (α : Type)
    (Γ : List (Formula α)) (seen ctx ty k : OTerm α) :
    Nonempty (Derivation body Γ (constructors (scanInvariant E seen ctx ty k))) := by
  apply actualFiniteUniversalIntroduction body α 3 Γ
    (constructorBody (scanInvariant E seen ctx ty k))
  let j : α → α ⊕ Fin 3 := Sum.inl
  let n : OTerm (α ⊕ Fin 3) := .var (.inr 0)
  let h : OTerm (α ⊕ Fin 3) := .var (.inr 1)
  let t : OTerm (α ⊕ Fin 3) := .var (.inr 2)
  let C := consGraph n h t
  let R := hitScan E t (seen.relabel j) (ctx.relabel j) (ty.relabel j) (k.relabel j)
  let Δ := R :: C :: Γ.map (fun p => p.relabel j)
  change Nonempty (Derivation body (Γ.map (fun p => p.relabel j))
    (C.imp ((atIndex (scanInvariant E seen ctx ty k) 2).imp
      (atIndex (scanInvariant E seen ctx ty k) 0))))
  simp only [scanInvariantIndex]
  obtain ⟨out⟩ := atCons (body := body) (Γ := Δ) E n h t (seen.relabel j) (ctx.relabel j)
    (ty.relabel j) (k.relabel j)
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction out)⟩

/-- Induction on the original scratch vertices code inside the original
calculus. Edge, seen, context, type and candidate are fixed; the filtered
output is selected by actual Program totality. -/
theorem retainedScan : ExactRetainedScan := by
  intro E body α Γ vertices seen ctx ty out k
  have base : Nonempty (Derivation body Γ (atCode (scanInvariant E seen ctx ty k) z)) := by
    rw [scanInvariantCode]
    exact atNil E seen ctx ty k
  obtain ⟨base⟩ := base
  obtain ⟨step⟩ := constructorDerivation E body α Γ seen ctx ty k
  have original : Nonempty (Derivation body Γ (premises (scanInvariant E seen ctx ty k))) :=
    ⟨Derivation.conjunctionIntroduction base step⟩
  have current := actualOriginalListInductionAtCode body α Γ (scanInvariant E seen ctx ty k)
    vertices original
  rw [scanInvariantCode] at current
  obtain ⟨law⟩ := current
  let P := passGraph E out vertices seen ctx ty ⊓ memberGraph out k
  have both : Derivation body (P :: Γ) P := Derivation.hypothesis List.mem_cons_self
  obtain ⟨hit⟩ := hitIntro (body := body) (Γ := P :: Γ) E out vertices seen ctx ty k
    ⟨Derivation.conjunctionLeft both⟩ ⟨Derivation.conjunctionRight both⟩
  have applied : Derivation body (P :: Γ) (scanGraph E seen ctx ty k) :=
    Derivation.implicationElimination (addHyp law P) hit
  exact ⟨Derivation.implicationIntroduction applied⟩

/-- The checked open scan witness at the very same seen code, context,
type and retained candidate. -/
theorem retainedPredecessor : ExactRetainedPredecessor := by
  intro E body α Γ vertices seen ctx ty out k
  let P := passGraph E out vertices seen ctx ty ⊓ memberGraph out k
  obtain ⟨law⟩ := retainedScan E body α (P :: Γ) vertices seen ctx ty out k
  obtain ⟨witness⟩ := exact_OpenDirectedSeenWitness E body α (P :: Γ) seen ctx ty k
  have both : Derivation body (P :: Γ) P := Derivation.hypothesis List.mem_cons_self
  have scanned : Derivation body (P :: Γ) (scanGraph E seen ctx ty k) :=
    Derivation.implicationElimination law both
  have found : Derivation body (P :: Γ) (seenWitness E seen ctx ty k) :=
    Derivation.implicationElimination witness scanned
  exact ⟨Derivation.implicationIntroduction found⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRetainedScanInductionProof
