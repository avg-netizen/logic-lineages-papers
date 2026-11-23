module
public import LogicLineages.PersistentMarking.NumberedWindowConcreteCheckers
import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepFieldProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowOriginalSelectRootFieldsProof
open NumberedWindowFieldAlgorithm (packNode unpackNode unpack)
open NumberedWindowAtomicRawStepFieldProof (nodePacked)
open NumberedWindowConcreteCheckers (root)
open NumberedWindowRootDispatchAlgorithm (check fixed parts flagView)
open NumberedWindowAddressAlgorithm (contextView)
open NumberedWindowSyntaxAlgorithm (syntaxBits termNext termParts)
open NumberedWindowMarkRootAlgorithm (guarded)
open NumberedWindowSelectAlgorithm (select chosen fromOwner body)
open NumberedWindowOwnerAlgorithm (owner plan applyCopies)
open NumberedWindowAnnotationAlgorithm (annotations arrow)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)

/-- Actual physical fields and chosen slot, with the original source
and target syntax guards and full ordered owner-copy result. -/
def SelectFields (src dst flag index domainCode : Nat) : Prop :=
  ∃ extra domains head result label base extras tape child,
    flagView flag = some extra ∧ contextView domainCode = some domains ∧
    (syntaxBits src).1 = true ∧ (syntaxBits dst).1 = true ∧
    unpackNode src = some (5,[head,result,label+1,base,extras]) ∧
    unpack (if extra then extras else base) = some tape ∧ tape[index]? = some child ∧
    (annotations child).1 = (plan result domains).1 ∧
    dst = applyCopies head label base extras child (plan result domains).2

/-- Literal ordered extension of the *original* plan and owner fold.
The first copy has its own domain as output, while the application
has the full residual arrow prefix as codomain. -/
theorem exact_OriginalSelectOwnerFoldCons
    (head label base extras child result dom : Nat) (domains : List Nat) :
    (plan result (dom::domains)).1 = arrow dom (plan result domains).1 ∧
    applyCopies head label base extras child (plan result (dom::domains)).2 =
      applyCopies head label base extras
        (packNode 6 [dom,(plan result domains).1,child,owner head label base extras dom])
        (plan result domains).2 := by
  exact ⟨rfl,rfl⟩

private theorem readFields (src dst index : Nat) (extra : Bool) (domains : List Nat)
    (h : select extra index domains src dst = true) :
    ∃ head result label base extras tape child,
      (syntaxBits src).1 = true ∧ (syntaxBits dst).1 = true ∧
      unpackNode src = some (5,[head,result,label+1,base,extras]) ∧
      unpack (if extra then extras else base) = some tape ∧ tape[index]? = some child ∧
      (annotations child).1 = (plan result domains).1 ∧
      dst = applyCopies head label base extras child (plan result domains).2 := by
  simp only [select,guarded,Bool.and_eq_true,and_assoc] at h
  obtain ⟨sx,sy,h⟩ := h
  cases seen : unpackNode src with
  | none => simp [seen] at h
  | some row =>
    rcases row with ⟨tag,slots⟩
    have ht : tag = 5 := by
      have b : ((tag == 5) && fromOwner extra index domains dst
          (slots.getD 0 0) (slots.getD 1 0) (slots.getD 2 0)
          (slots.getD 3 0) (slots.getD 4 0)) = true := by
        simpa only [seen,Option.any_some,body] using h
      simp only [Bool.and_eq_true,beq_iff_eq] at b
      exact b.1
    subst tag
    have shape := sx
    simp only [syntaxBits,termNext,seen,Option.any_some] at shape
    rcases slots with _ | ⟨f,_ | ⟨t,_ | ⟨label,_ | ⟨b,_ | ⟨e,_ | ⟨spare,rest⟩⟩⟩⟩⟩⟩ <;>
      simp [termParts] at shape
    have held : fromOwner extra index domains dst f t label b e = true := by
      simpa [seen,body,List.getD_eq_getElem?_getD] using h
    cases label with
    | zero => simp [fromOwner] at held
    | succ label =>
      cases got : unpack (if extra then e else b) with
      | none => simp [fromOwner,chosen,got] at held
      | some tape =>
        cases picked : tape[index]? with
        | none => simp [fromOwner,chosen,got,picked] at held
        | some child =>
          have tested : (annotations child).1 = (plan t domains).1 ∧
              applyCopies f label b e child (plan t domains).2 = dst := by
            simpa [fromOwner,chosen,got,picked,Bool.and_eq_true,beq_iff_eq] using held
          exact ⟨f,t,label,b,e,tape,child,sx,sy,
            by first | exact seen | rfl, by first | exact got | rfl,
            by first | exact picked | rfl,tested.1,tested.2.symm⟩

/-- Recover the actual supplied Select witness's flag, ordered domains
and exact index selection from the original root (no source AST encoding
premise). Other root tags are outside this theorem. -/
theorem exact_OriginalSelectRootFields (xs : Entries) (s : Settings)
    (src cert dst flag index domainCode : Nat)
    (witness : unpackNode cert = some (2,[flag,index,domainCode]))
    (h : root xs s src cert dst = true) :
    SelectFields src dst flag index domainCode := by
  cases fv : flagView flag with
  | none => simp [root,check,witness,parts,fv] at h
  | some extra =>
    cases ds : contextView domainCode with
    | none => simp [root,check,witness,parts,fv,ds] at h
    | some domains =>
      have real : select extra index domains src dst = true := by
        simpa [root,check,witness,parts,fv,ds,fixed] using h
      obtain ⟨head,result,label,base,extras,tape,child,sx,sy,seen,got,picked,ty,out⟩ :=
        readFields src dst index extra domains real
      exact ⟨extra,domains,head,result,label,base,extras,tape,child,fv,ds,sx,sy,seen,got,picked,ty,out⟩

#print axioms exact_OriginalSelectRootFields
#print axioms exact_OriginalSelectOwnerFoldCons
end LogicLineages.PersistentMarking.NumberedWindowOriginalSelectRootFieldsProof
