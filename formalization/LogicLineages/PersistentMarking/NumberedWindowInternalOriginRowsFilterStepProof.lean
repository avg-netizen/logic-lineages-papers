module
public import LogicLineages.PersistentMarking.NumberedWindowInternalOriginRowsFilterTargets
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceNormalizationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalOriginRowsFilterStepProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open LogicLineages.ComputabilityKnowledge GorbowPRProgram
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalListCodec (consCode)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchIntro zeroBranchElim successorBranchIntro successorBranchElim)
open ID1Completion.InternalAcceptanceNormalizationProof (normalizeAccept normalizeReject)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue valueUnique outputTransport)
open ID1Completion.InternalBetaTotalityProof (addHyp)
open GorbowVerifierNormalization (normalize)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalOriginRowsFilterTargets

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
local notation "T" => OrdinaryArithmetic.Term

private theorem selected (h rest pool dom : T α) (val : T α)
    (found : Report B Γ (unary (field 1) dom h))
    (mem : Report B Γ (programGraph scratchMember val ![pool,dom])) :
    Report B Γ (programGraph selectMember val ![h,rest,pool]) := by
  let xs : Fin 3 → T α := ![h,rest,pool]
  have fieldAt : Report B Γ (programGraph selectField dom xs) := by
    apply compositionValue (field 1) ![.projection 0] dom xs ![h] found
    intro i
    exact Fin.cases (projectionValue 0 xs) (fun j => Fin.elim0 j) i
  apply compositionValue scratchMember ![.projection 2,selectField] val xs ![pool,dom] mem
  intro i
  exact Fin.cases (projectionValue 2 xs) (Fin.cases fieldAt (fun j => Fin.elim0 j)) i

private theorem selectedBack (h rest pool dom val : T α)
    (found : Report B Γ (unary (field 1) dom h))
    (mem : Report B Γ (programGraph selectMember val ![h,rest,pool])) :
    Report B Γ (programGraph scratchMember val ![pool,dom]) := by
  let xs : Fin 3 → T α := ![h,rest,pool]
  have fieldAt : Report B Γ (programGraph selectField dom xs) := by
    apply compositionValue (field 1) ![.projection 0] dom xs ![h] found
    intro i
    exact Fin.cases (projectionValue 0 xs) (fun j => Fin.elim0 j) i
  apply compositionRecover scratchMember ![.projection 2,selectField] val xs ![pool,dom] mem
  intro i
  exact Fin.cases (projectionValue 2 xs) (Fin.cases fieldAt (fun j => Fin.elim0 j)) i

private theorem prependIff (out h rest pool : T α) :
    Report B Γ (programGraph prependRow out ![h,rest,pool]) ↔
      Report B Γ (rowCell out h rest) := by
  let xs : Fin 3 → T α := ![h,rest,pool]
  have args : ∀ i : Fin 2, Report B Γ (programGraph
      ((![.projection 0,.projection 1] : Fin 2 → Program 3) i) ((![h,rest] : Fin 2 → T α) i) xs) :=
    fun i => Fin.cases (projectionValue 0 xs)
      (Fin.cases (projectionValue 1 xs) (fun j => Fin.elim0 j)) i
  exact ⟨fun hw => compositionRecover consCode ![.projection 0,.projection 1] out xs ![h,rest] hw args,
    fun hc => compositionValue consCode ![.projection 0,.projection 1] out xs ![h,rest] hc args⟩

private theorem skipIff (out h rest pool : T α) :
    Report B Γ (programGraph (.projection (1 : Fin 3)) out ![h,rest,pool]) ↔
      Report B Γ (eqn out rest) := by
  let xs : Fin 3 → T α := ![h,rest,pool]
  have ref := projectionValue (body := B) (Gamma := Γ) 1 xs
  constructor
  · intro run
    exact valueUnique (.projection (1 : Fin 3)) out rest xs run ref
  · intro same
    obtain ⟨same⟩ := same
    exact outputTransport (.projection (1 : Fin 3)) rest out xs
      ⟨symm same⟩ ref

/-- Exact select/skip behavior on the same original row and unchanged tail
result. Both passes query the same fixed removed scratch list. -/
theorem exact_OpenOriginRowStep : ExactOpenOriginRowStep := by
  intro B α Γ h rest pool dom out fieldView
  let xs : Fin 3 → T α := ![h,rest,pool]
  let q := programGraph scratchMember (suc z) ![pool,dom]
  let p := programGraph selectMember (suc z) xs
  let n := normalize selectMember
  have build := prependIff (B := B) (Γ := Γ) out h rest pool
  have skip := skipIff (B := B) (Γ := Γ) out h rest pool
  constructor
  · intro member
    have on := normalizeAccept selectMember xs (selected h rest pool dom (suc z) fieldView member)
    constructor
    · exact ⟨fun run => build.mp (successorBranchElim n (.projection 1) prependRow out z xs on run),
        fun result => successorBranchIntro n (.projection 1) prependRow out z xs on (build.mpr result)⟩
    · exact ⟨fun run => skip.mp (successorBranchElim n prependRow (.projection 1) out z xs on run),
        fun result => successorBranchIntro n prependRow (.projection 1) out z xs on (skip.mpr result)⟩
  · intro missing
    have negative : Report B Γ p.not := by
      obtain ⟨missing⟩ := missing
      obtain ⟨fieldView⟩ := fieldView
      have hpos : Report B (p :: Γ) q := selectedBack h rest pool dom (suc z)
        ⟨addHyp fieldView p⟩ ⟨Derivation.hypothesis List.mem_cons_self⟩
      obtain ⟨hpos⟩ := hpos
      exact ⟨Derivation.implicationIntroduction
        (Derivation.implicationElimination (addHyp missing p) hpos)⟩
    have off := normalizeReject selectMember xs negative
    constructor
    · exact ⟨fun run => skip.mp (zeroBranchElim n (.projection 1) prependRow out xs off run),
        fun result => zeroBranchIntro n (.projection 1) prependRow out xs off (skip.mpr result)⟩
    · exact ⟨fun run => build.mp (zeroBranchElim n prependRow (.projection 1) out xs off run),
        fun result => zeroBranchIntro n prependRow (.projection 1) out xs off (build.mpr result)⟩

#print axioms exact_OpenOriginRowStep

end LogicLineages.PersistentMarking.NumberedWindowInternalOriginRowsFilterStepProof
