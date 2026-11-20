module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenConsBuildProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldExistentialProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenConsProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (projectionValue valueUnique outputTransport)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchIntro)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalLessThanSupportProof (zeroConstantValue)
open ID1Completion.InternalTagArithmeticSyntaxProof (z)
open NumberedWindowInternalSparseFieldInductionTargets (consGraph)
open NumberedWindowInternalSparseFieldExistentialProof (consGraphRename)
open NumberedWindowInternalSparseFieldParser
open NumberedWindowInternalSparseFieldParserTargets
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof
open NumberedWindowInternalSparseFieldParserOpenConsBuildProof (consFromPrepend)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem prependFromCons (o n h t r : OTerm α)
    (owner : Nonempty (Derivation body Γ (consGraph n h t)))
    (tail : Nonempty (Derivation body Γ (parserGraph r t)))
    (result : Nonempty (Derivation body Γ (parserGraph o n))) :
    Nonempty (Derivation body Γ (prependGraph o h r)) := by
  apply programCases prependResult ![h,r] _
  intro β j Δ v hJ out
  rw [prependRename]
  rw [binaryInputsRename] at out
  have owner' := renameInto owner j Δ hJ
  have tail' := renameInto tail j Δ hJ
  have result' := renameInto result j Δ hJ
  rw [consGraphRename] at owner'
  rw [parserRename] at tail'
  rw [parserRename] at result'
  have made := consFromPrepend v (n.relabel j) (h.relabel j) (t.relabel j) (r.relabel j)
    owner' tail' out
  have same := valueUnique parser v (o.relabel j) ![n.relabel j] made result'
  exact outputTransport prependResult v (o.relabel j) ![h.relabel j,r.relabel j] same out

private theorem prependZero (h : OTerm α) :
    Nonempty (Derivation body Γ (prependGraph z h z)) :=
  zeroBranchIntro (.projection 1) (constantZero 2) prependPayload z ![h,z]
    (projectionValue (1 : Fin 2) ![h,z]) (zeroConstantValue ![h,z])

theorem openCons : OpenConsRow := by
  intro body α n h t out tailResult
  let a := consGraph n h t ⊓ parserGraph tailResult t
  let selected := parserGraph out n
  let row := prependGraph out h tailResult
  have lbase : Derivation body [selected,a] a :=
    Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
  have rbase : Derivation body [row,a] a :=
    Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
  obtain ⟨left⟩ := prependFromCons out n h t tailResult
    ⟨Derivation.conjunctionLeft lbase⟩ ⟨Derivation.conjunctionRight lbase⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨right⟩ := consFromPrepend out n h t tailResult
    ⟨Derivation.conjunctionLeft rbase⟩ ⟨Derivation.conjunctionRight rbase⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction
    (Derivation.conjunctionIntroduction (Derivation.implicationIntroduction left)
      (Derivation.implicationIntroduction right))⟩

theorem rejectedTail : OpenRejectedTail := by
  intro body α n h t
  let a := consGraph n h t ⊓ parserGraph z t
  have d : Derivation body [a] a := Derivation.hypothesis List.mem_cons_self
  obtain ⟨out⟩ := consFromPrepend z n h t z
    ⟨Derivation.conjunctionLeft d⟩ ⟨Derivation.conjunctionRight d⟩ (prependZero h)
  exact ⟨Derivation.implicationIntroduction out⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenConsProof
