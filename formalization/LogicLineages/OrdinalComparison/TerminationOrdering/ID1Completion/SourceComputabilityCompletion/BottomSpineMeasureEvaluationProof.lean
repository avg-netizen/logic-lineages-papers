module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomSpineMeasureTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomRepresentativeEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeFoldCalibrationSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomSpineProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomSpineMeasureEvaluationProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedAuxiliaryCoding
open NumberedLeastCodeRepresentative NumberedQuotientApplication
open InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsEvaluationProof InternalApplicationStepPeelEvaluationSupportProof
open InternalAcceptanceCalibrationProof
open InternalParameterizedApplicationResultFoldCalibration InternalParameterizedApplicationResultFoldCalibrationProof
open InternalApplicationValidityStack (tagValue payloadValue functionChildValue)
open InternalRepresentativeFoldCalibrationSupportProof (applicationSelectors)
open SourceComputabilityCompletion.BottomSpineMeasure
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector

theorem tagEvaluation (value parameter : Nat) :
    evaluate (leftOf (rightOf (.projection (0 : Fin 2))))
      (ofFn ![value,parameter]) = tagValue value := by
  rw [leftOfEvaluation,rightOfEvaluation]
  rfl

theorem leafEvaluation (value parameter : Nat) :
    evaluate leaf (ofFn ![value,parameter]) = Nat.pair (if tagValue value = 3 then 1 else 0) 0 := by
  rw [leaf,pairOfEvaluation,sameEvaluation,tagEvaluation,
    BottomRepresentativeEvaluationProof.constantEvaluation]
  rfl

theorem combineEvaluation (d e f a parameter : Nat) :
    evaluate combine (ofFn ![d,e,f,a,parameter]) =
      Nat.pair (Nat.unpair f).1 ((Nat.unpair f).2 + 1) := by
  rw [combine,pairOfEvaluation,leftOfEvaluation]
  change Nat.pair (Nat.unpair f).1
    (evaluate (rightOf (.projection (2 : Fin 5))) (ofFn ![d,e,f,a,parameter]) + 1) = _
  rw [rightOfEvaluation]
  rfl

theorem foldSemanticEvaluation (value parameter : Nat) :
    evaluate fold (ofFn ![value,parameter]) =
      semanticFoldP (InternalLessThan.constantOne 2) leaf combine value parameter :=
  (actualOriginalParameterizedBoundedResultFoldCalibration
    (InternalLessThan.constantOne 2) leaf combine value parameter).2

theorem foldRecurrence (value parameter : Nat) :
    evaluate fold (ofFn ![value,parameter]) =
      if tagValue value = 2 then
        Nat.pair
          (Nat.unpair (evaluate fold (ofFn ![functionChildValue value,parameter]))).1
          ((Nat.unpair (evaluate fold (ofFn ![functionChildValue value,parameter]))).2 + 1)
      else Nat.pair (if tagValue value = 3 then 1 else 0) 0 := by
  have h := actualOriginalParameterizedSemanticResultFoldEquation
    (InternalLessThan.constantOne 2) leaf combine value parameter
  simp only [← foldSemanticEvaluation] at h
  rw [combineEvaluation,leafEvaluation] at h
  simpa only [InternalApplicationValidityStackEvaluationProof.oneEvaluation,
    and_true] using h

def syntaxTag {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {tau : Ty} :
    AuxTerm Symbol arity Gamma tau → Nat
  | .var _ => 0
  | .lam _ => 1
  | .app _ _ => 2
  | .bottom _ => 3
  | .ordinary _ _ => 4
  | .numbered _ _ _ _ _ _ => 5

theorem packedTag {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty} {tau : Ty}
    (q : AuxTerm (Fin n) arity Gamma tau) :
    tagValue (packedNumber (⟨tau,q⟩ : Packed (Fin n) arity Gamma)) = syntaxTag q := by
  cases q <;> simp only [syntaxTag,tagValue,payloadValue,packedNumber,termCode,codeNumber,Nat.unpair_pair]

theorem applicationRecurrence {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty} {sigma tau : Ty}
    (f : AuxTerm (Fin n) arity Gamma (.arrow sigma tau))
    (a : AuxTerm (Fin n) arity Gamma sigma) (parameter : Nat) :
    evaluate fold (ofFn ![packedNumber (⟨tau,.app f a⟩ : Packed (Fin n) arity Gamma),parameter]) =
      Nat.pair (Nat.unpair (evaluate fold (ofFn ![packedNumber ⟨.arrow sigma tau,f⟩,parameter]))).1
        ((Nat.unpair (evaluate fold (ofFn ![packedNumber ⟨.arrow sigma tau,f⟩,parameter]))).2 + 1) := by
  have hs : functionChildValue (packedNumber (⟨tau,.app f a⟩ : Packed (Fin n) arity Gamma)) =
      packedNumber ⟨.arrow sigma tau,f⟩ := by
    simpa only [applicationPacked] using (applicationSelectors f a).2.2.1
  rw [foldRecurrence,packedTag]
  simp only [syntaxTag,ite_true,hs]

theorem foldOnTerm (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (tau : Ty)
    (q : AuxTerm (Fin n) arity Gamma tau) (parameter : Nat) :
    evaluate fold (ofFn ![packedNumber (⟨tau,q⟩ : Packed (Fin n) arity Gamma),parameter]) = meaning q := by
  induction q using AuxTerm.rec (motive_2 := fun _ _ _ => True)
  case app f a ihf iha =>
    rw [applicationRecurrence,ihf]
    simp only [meaning,bottomFlag,NumberedBottomSpine.spineDepth,Nat.unpair_pair]
  case var =>
    rw [foldRecurrence]
    simp only [packedTag,syntaxTag,meaning,bottomFlag,NumberedBottomSpine.spineDepth,ite_false,ite_true,Nat.reduceEqDiff]
  case lam =>
    rw [foldRecurrence]
    simp only [packedTag,syntaxTag,meaning,bottomFlag,NumberedBottomSpine.spineDepth,ite_false,ite_true,Nat.reduceEqDiff]
  case bottom =>
    rw [foldRecurrence]
    simp only [packedTag,syntaxTag,meaning,bottomFlag,NumberedBottomSpine.spineDepth,ite_false,ite_true,Nat.reduceEqDiff]
  case ordinary =>
    rw [foldRecurrence]
    simp only [packedTag,syntaxTag,meaning,bottomFlag,NumberedBottomSpine.spineDepth,ite_false,ite_true,Nat.reduceEqDiff]
  case numbered =>
    rw [foldRecurrence]
    simp only [packedTag,syntaxTag,meaning,bottomFlag,NumberedBottomSpine.spineDepth,ite_false,ite_true,Nat.reduceEqDiff]
  case nil => trivial
  case cons => trivial

theorem measureEvaluation (value : Nat) :
    evaluate measure (ofFn ![value]) = evaluate fold (ofFn ![value,0]) := by
  change evaluate fold (ofFn fun i : Fin 2 =>
    evaluate ((![.projection 0,InternalAcceptance.constantZero 1] : Fin 2 → Program 1) i)
      (ofFn ![value])) = _
  have hv : (ofFn fun i : Fin 2 =>
      evaluate ((![.projection 0,InternalAcceptance.constantZero 1] : Fin 2 → Program 1) i)
        (ofFn ![value])) = ofFn ![value,0] := by
    apply List.Vector.ext
    intro i
    simp only [List.Vector.get_ofFn]
    refine Fin.cases ?_ (Fin.cases ?_ (fun k => Fin.elim0 k)) i <;> rfl
  rw [hv]

theorem flagMeaning {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {tau : Ty}
    (q : AuxTerm Symbol arity Gamma tau) :
    bottomFlag q = 1 ↔ NumberedBottomSpine.BottomSpine q := by
  induction q using AuxTerm.rec (motive_2 := fun _ _ _ => True)
  all_goals first | trivial | simp_all [bottomFlag,NumberedBottomSpine.BottomSpine]

theorem flagCases {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {tau : Ty}
    (q : AuxTerm Symbol arity Gamma tau) : bottomFlag q = 0 ∨ bottomFlag q = 1 := by
  induction q using AuxTerm.rec (motive_2 := fun _ _ _ => True)
  all_goals first | trivial | simp_all [bottomFlag]

theorem actualOriginalBottomSpineMeasureCalibration :
    BottomSpineMeasureTargets.ActualOriginalBottomSpineMeasureCalibration := by
  intro n arity Gamma tau q
  constructor
  · rw [measureEvaluation]
    exact foldOnTerm n arity Gamma tau q 0
  · exact flagMeaning q

theorem meaningPrimaryInvariant {Symbol : Type} {arity : Symbol → Nat}
    {symbols : List Symbol} {S Gamma : List Ty}
    {q r : Packed Symbol arity Gamma}
    (he : NumberedWindowEquivalence.WindowPrimary Symbol arity symbols S Gamma q r) :
    meaning q.2 = meaning r.2 := by
  have h := NumberedBottomSpineProof.actualPrimarySpineInvariant
    Symbol arity symbols S Gamma q r he
  have hf : bottomFlag q.2 = 1 ↔ bottomFlag r.2 = 1 :=
    (flagMeaning q.2).trans (h.1.trans (flagMeaning r.2).symm)
  have hg : bottomFlag q.2 = bottomFlag r.2 := by
    rcases flagCases q.2 with hq | hq
    · have hr : bottomFlag r.2 = 0 := (flagCases r.2).resolve_right (fun hr => by
        have hq1 := hf.mpr hr
        simp only [hq,Nat.zero_ne_one] at hq1)
      rw [hq,hr]
    · rw [hq,hf.mp hq]
  exact congrArg₂ Nat.pair hg h.2

/-- Native source calibration only: the ORIGINAL least representative has
the same full mark because primary equivalence preserves both quantities.
This theorem is never used as an internal reflection principle. -/
theorem representativeMeasure (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (hS : SubtypeClosed (fun tau => tau ∈ S))
    (q : Packed (Fin n) arity Gamma) (hq : NumberedFiniteUniverse.InUniverse symbols S q.2) :
    evaluate measure (ofFn ![representativeCode symbols S q]) =
      evaluate measure (ofFn ![packedNumber q]) := by
  obtain ⟨r,hr,he⟩ := NumberedLeastCodeRepresentativeProof.representativeAttained
    n arity symbols S hS Gamma q hq
  rw [he,measureEvaluation,measureEvaluation,foldOnTerm,foldOnTerm]
  exact (meaningPrimaryInvariant hr).symm

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomSpineMeasureEvaluationProof
