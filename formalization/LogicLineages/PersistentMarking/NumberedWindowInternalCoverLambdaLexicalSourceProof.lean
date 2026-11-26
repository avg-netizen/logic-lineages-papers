module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalSourceTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalDischargeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaProvenanceProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepFieldProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalSourceProof
open NumberedWindowScalarAlgorithm (Settings admitted)
open NumberedWindowAnnotationAlgorithm (arrow annotations)
open NumberedWindowFieldAlgorithm (pack unpack unpackNode)
open NumberedWindowLexicalAlgorithm (requirements typed holds binder)
open NumberedWindowSyntaxAlgorithm (syntaxBits)
open NumberedWindowAdmissionAlgorithm (bits rawBits)
open NumberedWindowAtomicRawStepFieldProof (unpackPacked)
open NumberedWindowInternalSparseTypedRawTargets (packedWindow)
open NumberedWindowInternalAuxWindowMemoTargets (intrinsicWindow intrinsicType)
open NumberedWindowInternalCoverLambdaProvenanceProof (exact_CoverLambdaSourceProvenance)
open NumberedWindowInternalCoverLambdaLexicalDischargeProof (exact_CoverRawLexicalBinder)
open NumberedWindowInternalCoverLambdaLexicalSourceTargets

private theorem previous {X : Type} (tab : Nat → List X) (row : Nat → X)
    (init : tab 0 = []) (step : ∀ n, tab (n+1) = tab n ++ [row n]) :
    ∀ {i n : Nat}, i < n → (tab n)[i]? = some (row i) := by
  have length (n : Nat) : (tab n).length = n := by
    induction n with
    | zero => rw [init]; rfl
    | succ n ih => simp only [step,List.length_append,List.length_cons,List.length_nil,zero_add,ih]
  intro i n small
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases before : i < n
    · have within : i < (tab n).length := by
        rw [length n]
        exact before
      rw [step n,List.getElem?_append_left (l₁ := tab n) (l₂ := [row n]) within]
      exact ih before
    · have last : i = n := by omega
      subst i
      rw [step]
      simpa only [length] using (List.getElem?_concat_length (l := tab n) (a := row n))

private theorem oldAnn {i n : Nat} (small : i < n) :
    (NumberedWindowAnnotationAlgorithm.table n).getD i default = annotations i := by
  rw [List.getD_eq_getElem?_getD,previous NumberedWindowAnnotationAlgorithm.table annotations rfl
    (fun _ => rfl) small]
  rfl

private theorem oldLex {i n : Nat} (small : i < n) :
    (NumberedWindowLexicalAlgorithm.table n).getD i default = requirements i := by
  rw [List.getD_eq_getElem?_getD,previous NumberedWindowLexicalAlgorithm.table requirements rfl
    (fun _ => rfl) small]
  rfl

private theorem oldAdm (s : Settings) {i n : Nat} (small : i < n) :
    (NumberedWindowAdmissionAlgorithm.table s.window n).getD i (false,false) = rawBits s.window i := by
  rw [List.getD_eq_getElem?_getD,previous (NumberedWindowAdmissionAlgorithm.table s.window)
    (rawBits s.window) rfl (fun _ => rfl) small]
  rfl

theorem exact_CoverLambdaPackedLexicalProvenance : ExactCoverLambdaPackedLexicalProvenance := by
  intro s ctx raw domain child parsed positive
  obtain ⟨small,syntaxParts,_⟩ := exact_CoverLambdaSourceProvenance raw domain child parsed
  have d₀ : ([domain,child] : List Nat).getD 0 0 = domain := rfl
  have d₁ : ([domain,child] : List Nat).getD 1 0 = child := rfl
  have annotation : intrinsicType raw = arrow domain (intrinsicType child) := by
    simp only [intrinsicType,annotations,NumberedWindowAnnotationAlgorithm.termNext,parsed,Option.map_some,
      Option.getD_some,NumberedWindowAnnotationAlgorithm.termParts,d₀,d₁,oldAnn small]
  have req : (requirements raw).1 = binder domain (requirements child).1 := by
    simp only [requirements,NumberedWindowLexicalAlgorithm.termNext,parsed,Option.map_some,
      Option.getD_some,NumberedWindowLexicalAlgorithm.termParts,d₀,d₁,oldLex small]
  have admittedRow : (rawBits s.window raw).1 =
      (s.window.1.contains (arrow domain (intrinsicType child)) &&
        s.window.1.contains domain && (rawBits s.window child).1) := by
    simp only [rawBits,NumberedWindowAdmissionAlgorithm.termNext,parsed,Option.any_some,
      NumberedWindowAdmissionAlgorithm.termParts,d₀,d₁,oldAdm s small,intrinsicType]
  have selected : packedWindow s ctx (intrinsicType raw) raw = true := by
    cases h : packedWindow s ctx (intrinsicType raw) raw
    · exact False.elim (positive (by simp [intrinsicWindow,h]))
    · rfl
  have out : intrinsicWindow s ctx raw = arrow domain (intrinsicType child) + 1 := by
    rw [intrinsicWindow,if_pos selected,annotation]
  cases hctx : unpack ctx with
  | none => simp [packedWindow,hctx] at selected
  | some g =>
    have real : admitted s g (intrinsicType raw) raw = true := by
      simpa only [packedWindow,hctx,Option.any_some] using selected
    have typedParent : typed g (intrinsicType raw) raw = true := (Bool.and_eq_true_iff.mp real).1
    have admittedParent : ((syntaxBits raw).1 && (rawBits s.window raw).1) = true :=
      (Bool.and_eq_true_iff.mp real).2
    have syntaxParent : (syntaxBits raw).1 = true := (Bool.and_eq_true_iff.mp admittedParent).1
    have syntaxChild := (syntaxParts.mp syntaxParent).2
    have lexParent : holds (fun i => g[i]?) (requirements raw).1 = true :=
      (Bool.and_eq_true_iff.mp typedParent).2
    rw [req,exact_CoverRawLexicalBinder] at lexParent
    have rawParent : (rawBits s.window raw).1 = true := (Bool.and_eq_true_iff.mp admittedParent).2
    rw [admittedRow] at rawParent
    have rawChild := (Bool.and_eq_true_iff.mp rawParent).2
    have domMember := List.contains_iff_mem.mp ((Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp rawParent).1).2)
    have typedChild : typed (domain::g) (intrinsicType child) child = true := by
      simp [typed,syntaxChild,lexParent,intrinsicType]
    have admitsChild : admitted s (domain::g) (intrinsicType child) child = true := by
      simp [admitted,typedChild,bits,syntaxChild,rawChild]
    have childQuery : packedWindow s (pack (domain::g)) (intrinsicType child) child = true := by
      rw [packedWindow,unpackPacked]
      exact admitsChild
    have childValue : intrinsicWindow s (pack (domain::g)) child = intrinsicType child + 1 := by
      rw [intrinsicWindow,if_pos childQuery]
    refine ⟨g,?_,domMember,childValue,out⟩
    first | exact hctx | rfl

#print axioms exact_CoverLambdaPackedLexicalProvenance

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalSourceProof
