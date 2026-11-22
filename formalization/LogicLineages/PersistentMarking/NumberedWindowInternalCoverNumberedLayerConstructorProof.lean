module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedLayerTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedLayerOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCartesianFoldSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCartesianFoldThinOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenMemberConsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedLayerConstructorProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (z)
open ID1Completion.InternalTagArithmeticSupportProof (refl)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename quadInputsRename)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparseScratchMembershipOpenMemberConsProof (headMember)
open NumberedWindowInternalCoverCartesianFoldTargets (flatGraph)
open NumberedWindowInternalCoverCartesianFoldSyntaxProof (flatRename)
open NumberedWindowInternalCoverCartesianFoldThinOpenProof (exact_OpenCartesianFoldMember)
open NumberedWindowInternalCoverNumberedLayerTargets
open NumberedWindowInternalCoverNumberedLayerOpenDataProof

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem atSuffix (out args h ty k l r : OTerm α)
    (run : Nonempty (Derivation body Γ (flatGraph singletonNumbered out args ![h,ty,k,l])))
    (hr : Nonempty (Derivation body Γ (memberGraph args r))) :
    Nonempty (Derivation body Γ (memberGraph out (numberedTerm h ty k l r))) := by
  apply programCases singletonNumbered ![r,h,ty,k,l] _
  intro β j Δ block keep row
  rw [graphRename,numberedRename]
  simp only [quintInputsRename] at row
  have folded := renameInto run j Δ keep
  rw [flatRename,quadInputsRename] at folded
  have hr' := renameInto hr j Δ keep
  simp only [graphRename] at hr'
  let key := numberedTerm (h.relabel j) (ty.relabel j) (k.relabel j) (l.relabel j) (r.relabel j)
  have cell := singletonCell block (h.relabel j) (ty.relabel j) (k.relabel j) (l.relabel j) (r.relabel j) row
  have known := headMember block key z key cell ⟨refl key⟩
  exact exact_OpenCartesianFoldMember singletonNumbered body β Δ (args.relabel j) (r.relabel j) block key
    (out.relabel j) ![h.relabel j,ty.relabel j,k.relabel j,l.relabel j] hr' row known folded

private theorem atPrefix (out args h ty k l r : OTerm α)
    (run : Nonempty (Derivation body Γ (flatGraph prefixBlock out args ![args,h,ty,k])))
    (hl : Nonempty (Derivation body Γ (memberGraph args l)))
    (hr : Nonempty (Derivation body Γ (memberGraph args r))) :
    Nonempty (Derivation body Γ (memberGraph out (numberedTerm h ty k l r))) := by
  apply programCases prefixBlock ![l,args,h,ty,k] _
  intro β j Δ block keep row
  rw [graphRename,numberedRename]
  simp only [quintInputsRename] at row
  have folded := renameInto run j Δ keep
  rw [flatRename,quadInputsRename] at folded
  have hl' := renameInto hl j Δ keep
  have hr' := renameInto hr j Δ keep
  simp only [graphRename] at hl' hr'
  let key := numberedTerm (h.relabel j) (ty.relabel j) (k.relabel j) (l.relabel j) (r.relabel j)
  have inner := fromPrefix block (l.relabel j) (args.relabel j) (h.relabel j) (ty.relabel j) (k.relabel j) row
  have known := atSuffix block (args.relabel j) (h.relabel j) (ty.relabel j) (k.relabel j) (l.relabel j) (r.relabel j)
    inner hr'
  exact exact_OpenCartesianFoldMember prefixBlock body β Δ (args.relabel j) (l.relabel j) block key
    (out.relabel j) ![args.relabel j,h.relabel j,ty.relabel j,k.relabel j] hl' row known folded

private theorem atId (out ids args h ty k l r : OTerm α)
    (run : Nonempty (Derivation body Γ (flatGraph idBlock out ids ![args,h,ty])))
    (hk : Nonempty (Derivation body Γ (memberGraph ids k)))
    (hl : Nonempty (Derivation body Γ (memberGraph args l)))
    (hr : Nonempty (Derivation body Γ (memberGraph args r))) :
    Nonempty (Derivation body Γ (memberGraph out (numberedTerm h ty k l r))) := by
  apply programCases idBlock ![k,args,h,ty] _
  intro β j Δ block keep row
  rw [graphRename,numberedRename]
  simp only [quadInputsRename] at row
  have folded := renameInto run j Δ keep
  rw [flatRename,tripleInputsRename] at folded
  have hk' := renameInto hk j Δ keep
  have hl' := renameInto hl j Δ keep
  have hr' := renameInto hr j Δ keep
  simp only [graphRename] at hk' hl' hr'
  let key := numberedTerm (h.relabel j) (ty.relabel j) (k.relabel j) (l.relabel j) (r.relabel j)
  have inner := fromId block (k.relabel j) (args.relabel j) (h.relabel j) (ty.relabel j) row
  have known := atPrefix block (args.relabel j) (h.relabel j) (ty.relabel j) (k.relabel j) (l.relabel j) (r.relabel j)
    inner hl' hr'
  exact exact_OpenCartesianFoldMember idBlock body β Δ (ids.relabel j) (k.relabel j) block key
    (out.relabel j) ![args.relabel j,h.relabel j,ty.relabel j] hk' row known folded

private theorem atType (out K ids args h ty k l r : OTerm α)
    (run : Nonempty (Derivation body Γ (flatGraph typeBlock out K ![ids,args,h])))
    (ht : Nonempty (Derivation body Γ (memberGraph K ty)))
    (hk : Nonempty (Derivation body Γ (memberGraph ids k)))
    (hl : Nonempty (Derivation body Γ (memberGraph args l)))
    (hr : Nonempty (Derivation body Γ (memberGraph args r))) :
    Nonempty (Derivation body Γ (memberGraph out (numberedTerm h ty k l r))) := by
  apply programCases typeBlock ![ty,ids,args,h] _
  intro β j Δ block keep row
  rw [graphRename,numberedRename]
  simp only [quadInputsRename] at row
  have folded := renameInto run j Δ keep
  rw [flatRename,tripleInputsRename] at folded
  have ht' := renameInto ht j Δ keep
  have hk' := renameInto hk j Δ keep
  have hl' := renameInto hl j Δ keep
  have hr' := renameInto hr j Δ keep
  simp only [graphRename] at ht' hk' hl' hr'
  let key := numberedTerm (h.relabel j) (ty.relabel j) (k.relabel j) (l.relabel j) (r.relabel j)
  have inner := fromType block (ty.relabel j) (ids.relabel j) (args.relabel j) (h.relabel j) row
  have known := atId block (ids.relabel j) (args.relabel j) (h.relabel j) (ty.relabel j) (k.relabel j) (l.relabel j) (r.relabel j)
    inner hk' hl' hr'
  exact exact_OpenCartesianFoldMember typeBlock body β Δ (K.relabel j) (ty.relabel j) block key
    (out.relabel j) ![ids.relabel j,args.relabel j,h.relabel j] ht' row known folded

private theorem atHead (out H K ids args h ty k l r : OTerm α)
    (run : Nonempty (Derivation body Γ (flatGraph headBlock out H ![K,ids,args])))
    (hh : Nonempty (Derivation body Γ (memberGraph H h)))
    (ht : Nonempty (Derivation body Γ (memberGraph K ty)))
    (hk : Nonempty (Derivation body Γ (memberGraph ids k)))
    (hl : Nonempty (Derivation body Γ (memberGraph args l)))
    (hr : Nonempty (Derivation body Γ (memberGraph args r))) :
    Nonempty (Derivation body Γ (memberGraph out (numberedTerm h ty k l r))) := by
  apply programCases headBlock ![h,K,ids,args] _
  intro β j Δ block keep row
  rw [graphRename,numberedRename]
  simp only [quadInputsRename] at row
  have folded := renameInto run j Δ keep
  rw [flatRename,tripleInputsRename] at folded
  have hh' := renameInto hh j Δ keep
  have ht' := renameInto ht j Δ keep
  have hk' := renameInto hk j Δ keep
  have hl' := renameInto hl j Δ keep
  have hr' := renameInto hr j Δ keep
  simp only [graphRename] at hh' ht' hk' hl' hr'
  let key := numberedTerm (h.relabel j) (ty.relabel j) (k.relabel j) (l.relabel j) (r.relabel j)
  have inner := fromHead block (h.relabel j) (K.relabel j) (ids.relabel j) (args.relabel j) row
  have known := atType block (K.relabel j) (ids.relabel j) (args.relabel j) (h.relabel j) (ty.relabel j) (k.relabel j) (l.relabel j) (r.relabel j)
    inner ht' hk' hl' hr'
  exact exact_OpenCartesianFoldMember headBlock body β Δ (H.relabel j) (h.relabel j) block key
    (out.relabel j) ![K.relabel j,ids.relabel j,args.relabel j] hh' row known folded

theorem exact_OpenCoverNumberedLayerConstructor : ExactOpenCoverNumberedLayerConstructor := by
  intro body α Γ out H K ids args h ty k l r run hh ht hk hl hr
  exact atHead out H K ids args h ty k l r (outerGraph out H K ids args run) hh ht hk hl hr

#print axioms exact_OpenCoverNumberedLayerConstructor

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedLayerConstructorProof
