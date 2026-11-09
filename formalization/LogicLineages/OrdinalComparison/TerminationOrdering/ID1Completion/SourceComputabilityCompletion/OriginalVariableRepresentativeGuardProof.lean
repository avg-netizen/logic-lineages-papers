module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableRepresentativeTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomRepresentativeInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldClosureBridgeBranchProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableRepresentativeGuardProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open SourceComputabilityCompletion.OriginalVariableRepresentative
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof
open InternalControlGraphSupportProof InternalControlGraphChoiceProof
open InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalAcceptanceBranchProof
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalApplicationCertifiedResultFoldClosureBridgeBranchProof
open InternalTagArithmeticSyntaxProof (OTerm z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof (symm trans refl)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalPositiveUnfoldingSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

open SourceComputabilityCompletion.BottomRepresentativeInternalProof (indicatorIff)

def queries (R : Program 2) : Fin 4 → Program 2 :=
  Fin.cons R (Fin.cons (.composition variableMark (fun _ : Fin 1 => R))
    (Fin.cons (.composition variableMark (fun _ : Fin 1 => .projection 0))
      (Fin.cons (sameMark R) Fin.elim0)))

theorem query0 (R : Program 2) : queries R (0 : Fin 4) = R := rfl
theorem query1 (R : Program 2) : queries R (1 : Fin 4) =
    .composition variableMark (fun _ : Fin 1 => R) := rfl
theorem query2 (R : Program 2) : queries R (2 : Fin 4) =
    .composition variableMark (fun _ : Fin 1 => .projection 0) := rfl
theorem query3 (R : Program 2) : queries R (3 : Fin 4) = sameMark R := rfl

theorem markIffRename {β : Type} (indicator out input : OTerm α) (j : α → β) :
    ((markGraph indicator out).iff (markGraph indicator input)).relabel j =
      (markGraph (indicator.relabel j) (out.relabel j)).iff
        (markGraph (indicator.relabel j) (input.relabel j)) := by
  change ((graph1 variableMark indicator out).relabel j).iff
    ((graph1 variableMark indicator input).relabel j) =
    (graph1 variableMark (indicator.relabel j) (out.relabel j)).iff
      (graph1 variableMark (indicator.relabel j) (input.relabel j))
  rw [graph1Rename,graph1Rename]

theorem innerAtValues (R : Program 2) (out input parameter indicator candidate bx bi control : OTerm α)
    (hr : Nonempty (Derivation body Gamma (graph2 R candidate input parameter)))
    (hx : Nonempty (Derivation body Gamma (markGraph bx candidate)))
    (hi : Nonempty (Derivation body Gamma (markGraph bi input)))
    (hc : Nonempty (Derivation body Gamma (graph2 (sameMark R) control input parameter)))
    (hw : Nonempty (Derivation body Gamma
      (graph2 (InternalAcceptance.branch (sameMark R) (.projection 0) R) out input parameter))) :
    Nonempty (Derivation body Gamma ((markGraph indicator out).iff (markGraph indicator input))) := by
  let xs : Fin 2 → OTerm α := Fin.cons input (Fin.cons parameter Fin.elim0)
  have hleft : Nonempty (Derivation body Gamma
      (programGraph (.composition variableMark (fun _ : Fin 1 => R)) bx xs)) := by
    apply compositionValue variableMark (fun _ : Fin 1 => R) bx xs (Fin.cons candidate Fin.elim0) hx
    intro i
    exact Fin.cases hr (fun j => Fin.elim0 j) i
  have hright : Nonempty (Derivation body Gamma
      (programGraph (.composition variableMark (fun _ : Fin 1 => .projection 0)) bi xs)) := by
    apply compositionValue variableMark (fun _ : Fin 1 => .projection 0) bi xs (Fin.cons input Fin.elim0) hi
    intro i
    exact Fin.cases (projectionValue 0 xs) (fun j => Fin.elim0 j) i
  have hcompare : Nonempty (Derivation body Gamma
      (InternalEqualityTestCompositionProof.equalityGraph control bx bi)) := by
    apply compositionRecover InternalEqualityTest.equalityTest
      ![.composition variableMark (fun _ : Fin 1 => R),
        .composition variableMark (fun _ : Fin 1 => .projection 0)] control xs
      (Fin.cons bx (Fin.cons bi Fin.elim0)) hc
    intro i
    exact Fin.cases hleft (Fin.cases hright (fun j => Fin.elim0 j)) i
  apply formulaCases (eqn control z)
  · let P := eqn control z
    have hc0 := outputTransport (sameMark R) control z xs
      ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hc P)
    have ho := zeroBranchElim (sameMark R) (.projection 0) R out xs hc0 (withHyp hw P)
    obtain ⟨he⟩ := valueUnique (.projection (0 : Fin 2)) out input xs ho (projectionValue 0 xs)
    have hout := headTransport variableMark bi input out Fin.elim0 ⟨symm he⟩ (withHyp hi P)
    exact indicatorIff variableMark indicator out input bi bi hout (withHyp hi P) ⟨refl bi⟩
  · let P := (eqn control z).not
    have ho := nonzeroBranchElim (sameMark R) (.projection 0) R out control xs
      (withHyp hc P) ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hw P)
    obtain ⟨he⟩ := valueUnique R out candidate xs ho (withHyp hr P)
    have hbottom := equalityOfNonzero bx bi control (withHyp hcompare P)
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hout := headTransport variableMark bx candidate out Fin.elim0 ⟨symm he⟩ (withHyp hx P)
    exact indicatorIff variableMark indicator out input bx bi hout (withHyp hi P) hbottom

theorem atQueryValues (R : Program 2) (out input parameter indicator candidate bx bi control : OTerm α)
    (hw : Nonempty (Derivation body Gamma
      (graph2 (InternalAcceptance.branch (sameMark R) (.projection 0) R) out input parameter)))
    (hr : Nonempty (Derivation body Gamma (graph2 R candidate input parameter)))
    (hxq : Nonempty (Derivation body Gamma
      (programGraph (.composition variableMark (fun _ : Fin 1 => R)) bx
        (Fin.cons input (Fin.cons parameter Fin.elim0)))))
    (hiq : Nonempty (Derivation body Gamma
      (programGraph (.composition variableMark (fun _ : Fin 1 => .projection 0)) bi
        (Fin.cons input (Fin.cons parameter Fin.elim0)))))
    (hc : Nonempty (Derivation body Gamma (graph2 (sameMark R) control input parameter))) :
    Nonempty (Derivation body Gamma ((markGraph indicator out).iff (markGraph indicator input))) := by
  let xs : Fin 2 → OTerm α := Fin.cons input (Fin.cons parameter Fin.elim0)
  have hx := compositionRecover variableMark (fun _ : Fin 1 => R) bx xs
    (Fin.cons candidate Fin.elim0) hxq (fun i => Fin.cases hr (fun q => Fin.elim0 q) i)
  have hi := compositionRecover variableMark (fun _ : Fin 1 => .projection 0) bi xs
    (Fin.cons input Fin.elim0) hiq
    (fun i => Fin.cases (projectionValue 0 xs) (fun q => Fin.elim0 q) i)
  exact innerAtValues R out input parameter indicator candidate bx bi control hr hx hi hc hw

theorem innerPreservation (R : Program 2) (out input parameter indicator : OTerm α)
    (hw : Nonempty (Derivation body Gamma
      (graph2 (InternalAcceptance.branch (sameMark R) (.projection 0) R) out input parameter))) :
    Nonempty (Derivation body Gamma ((markGraph indicator out).iff (markGraph indicator input))) := by
  let xs : Fin 2 → OTerm α := Fin.cons input (Fin.cons parameter Fin.elim0)
  apply queryCases (queries R) xs _
  intro β j ys Delta hj hys
  rw [markIffRename]
  simp only [xs,consTermRename,emptyRename] at hys
  have hw' := renameInto hw j Delta hj
  rw [graph2Rename] at hw'
  have hr := hys 0
  rw [query0] at hr
  have hx := hys 1
  rw [query1] at hx
  have hi := hys 2
  rw [query2] at hi
  have hc := hys 3
  rw [query3] at hc
  exact atQueryValues R (out.relabel j) (input.relabel j) (parameter.relabel j) (indicator.relabel j)
    (ys 0) (ys 1) (ys 2) (ys 3) hw' hr hx hi hc

theorem preservation (data : InternalOriginalUniformDescentSelection.Data) (window : Program 1)
    (out value parameter indicator : OTerm α)
    (ha : Nonempty (Derivation body Gamma (graph2 (active data window) InternalOriginalStepGuard.one value parameter)))
    (hr : Nonempty (Derivation body Gamma (graph2 (representative data window) out value parameter))) :
    Nonempty (Derivation body Gamma ((markGraph indicator out).iff (markGraph indicator value))) := by
  have h := successorBranchElim (active data window) data.oldRepresentative
    (InternalAcceptance.branch (sameMark data.oldRepresentative) (.projection 0) data.oldRepresentative)
    out z (Fin.cons value (Fin.cons parameter Fin.elim0)) ha hr
  exact innerPreservation data.oldRepresentative out value parameter indicator h

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableRepresentativeGuardProof
