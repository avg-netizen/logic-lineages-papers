module

public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxWindowOpenTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestCompositionProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAuxWindowOpenQueryProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover programCases)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue successorValue outputTransport programRename)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestProof (equalityOfAcceptance)
open ID1Completion.InternalEqualityTestCompositionProof (equalitySelf)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename tripleInputsRename)
open NumberedWindowInternalAuxWindowStepTargets (intrinsicQuery)
open NumberedWindowInternalAuxWindowOpenTargets

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private def calls (F : Program 2) : Fin 2 → Program 3 :=
  ![.composition F ![.projection 0,.projection 2], .composition .succ ![.projection 1] ]

private theorem reports (F : Program 2) (out ctx ty raw : OTerm α)
    (h : Nonempty (Derivation body Γ (intrinsicGraph F out ctx raw))) :
    ∀ k : Fin 2, Nonempty (Derivation body Γ (programGraph (calls F k)
      ((![out,suc ty] : Fin 2 → OTerm α) k) ![ctx,ty,raw])) := by
  have actual : Nonempty (Derivation body Γ (programGraph (calls F 0) out ![ctx,ty,raw])) := by
    apply compositionValue F ![.projection 0,.projection 2] out ![ctx,ty,raw] ![ctx,raw] h
    intro i
    exact Fin.cases (projectionValue 0 ![ctx,ty,raw])
      (Fin.cases (projectionValue 2 ![ctx,ty,raw]) (fun j => Fin.elim0 j)) i
  have next : Nonempty (Derivation body Γ (programGraph (calls F 1) (suc ty) ![ctx,ty,raw])) := by
    apply compositionValue .succ ![.projection 1] (suc ty) ![ctx,ty,raw] ![ty] (successorValue ![ty])
    intro i
    obtain rfl := Fin.eq_zero i
    exact projectionValue 1 ![ctx,ty,raw]
  intro i
  exact Fin.cases actual (Fin.cases next (fun j => Fin.elim0 j)) i

attribute [local irreducible] programGraph in
theorem exact_OpenIntrinsicQuery : ExactOpenIntrinsicQuery := by
  intro F body α Γ ctx ty raw
  constructor
  · intro query
    apply programCases F ![ctx,raw] _
    intro β j Δ out hJ physical
    simp only [intrinsicGraph,programRename,binaryInputsRename,sucRelabel]
    simp only [binaryInputsRename] at physical
    have q := renameInto query j Δ hJ
    simp only [windowGraph,programRename,tripleInputsRename,sucRelabel,zRelabel] at q
    let ctx' := ctx.relabel j
    let ty' := ty.relabel j
    let raw' := raw.relabel j
    let input : Fin 3 → OTerm β := ![ctx',ty',raw']
    let result : Fin 2 → OTerm β := ![out,suc ty']
    have bit : Nonempty (Derivation body Δ (programGraph equalityTest (suc z) result)) :=
      compositionRecover equalityTest (calls F) (suc z) input result q (reports F out ctx' ty' raw' physical)
    exact outputTransport F out (suc ty') ![ctx',raw'] (equalityOfAcceptance out (suc ty') bit) physical
  · intro h
    exact compositionValue equalityTest (calls F) (suc z) ![ctx,ty,raw] ![suc ty,suc ty]
      (equalitySelf (suc ty)) (reports F (suc ty) ctx ty raw h)

end LogicLineages.PersistentMarking.NumberedWindowInternalAuxWindowOpenQueryProof
