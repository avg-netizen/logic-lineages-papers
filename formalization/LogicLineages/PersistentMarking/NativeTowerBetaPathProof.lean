import LogicLineages.PersistentMarking.NativeTowerBetaPathTargets
import LogicLineages.PersistentMarking.NativeTowerBetaBinderProof
import LogicLineages.PersistentMarking.NativeClosedBetaChecks
import LogicLineages.PersistentMarking.NativeClosedApplicationChecks
import LogicLineages.PersistentMarking.NativeOrdinalExponentialTypingProof
import LogicLineages.PersistentMarking.ClosedSyntaxProof
import LogicLineages.PersistentMarking.SubstitutionProof

namespace LogicLineages.PersistentMarking.NativeTowerBetaPathProof
open Spine NativeReduction StructuralContext NativeCarrierTargets NativeIndexedCarrierTargets NativeIteratorStrictTargets
open NativeClosedApplication NativeOrdinalArithmeticTargets NativeOrdinalExponentialTargets
open NativeTowerExtractorTargets NativeTowerExtractorGeneralTargets NativeTowerExtractorGeneralProof
open NativeTowerWitnessPrefixTargets NativeTowerWitnessPrefixProof
open NativeTowerWitnessFamilyTargets NativeTowerWitnessFamilyProof
open NativeTowerBetaBinderProof NativeTowerBetaPathTargets

def actualArg (S : Signature) : (k : Nat) → ClosedNativeTerm S (ty (k+1))
  | 0 => nativeNb S
  | k+1 => ⟨extractor k,extractorClosed S k⟩

theorem actualArgLiteral (S : Signature) (k : Nat) : (actualArg S k).val = binderArg k := by
  cases k <;> rfl

/-- Reinstall just the original still-pending typed right operands,
and retain the final outer t0 argument even when no binders remain. -/
def applyRemaining (S : Signature) : (k : Nat) →
    ClosedNativeTerm S (ty (k+1)) → ClosedNativeTerm S indexType
  | 0, f => applyClosed f (closedT0 S)
  | k+1, f => applyRemaining S k (applyClosed f (actualArg S k))

theorem applyRemainingLiteral (S : Signature) (l : Nat) :
    ∀ (f : ClosedNativeTerm S (ty (l+2))),
      (applyRemaining S (l+1) f).val =
        app indexType indexType (app endo endo (printedLower l f.val) nativeNB) t0 := by
  induction l with
  | zero => intro f; rfl
  | succ l ih =>
    intro f
    exact ih (applyClosed f (actualArg S (l+1)))

private theorem liftApplication (before after : ClosedNativeTerm S (.arrow σ τ))
    (arg : ClosedNativeTerm S σ) (step : BetaStep S before after) :
    BetaStep S (applyClosed before arg) (applyClosed after arg) := by
  let C : Context := .head (.app σ τ) .nil .hole (.cons arg.val .nil)
  have typed : ContextTyped S C (.arrow σ τ) τ :=
    .head .hole ⟨0,rfl⟩ .nil True.intro True.intro (.cons arg.property.1.1.1 .nil)
      ⟨arg.property.1.1.2,True.intro⟩ ⟨arg.property.1.2.1,True.intro⟩ rfl
  have raw : Reduction S (applyClosed before arg).val (applyClosed after arg).val := by
    change Reduction S (fill C before.val) (fill C after.val)
    exact .context typed before.property.1.1 after.property.1.1 step.reduction
  exact ⟨.underApp step.beta arg,raw,
    NativeClosedApplicationChecks.exact_NativeApplicationFunctionStrict S σ τ before after arg step.strict⟩

private theorem liftRemaining (S : Signature) (k : Nat) :
    ∀ (before after : ClosedNativeTerm S (ty (k+1))), BetaStep S before after →
      BetaStep S (applyRemaining S k before) (applyRemaining S k after) := by
  induction k with
  | zero =>
    intro before after step
    exact liftApplication before after (closedT0 S) step
  | succ k ih =>
    intro before after step
    exact ih _ _ (liftApplication before after (actualArg S k) step)

/-- Exact literal pending source and the real closed-native certificate
are the only helper inputs. No beta edge or closure of the next head is
assumed. -/
private theorem consumePending (S : Signature) (body : Expr) (k : Nat) :
    ∀ (outer : Args) (f : ClosedNativeTerm S (ty (k+1))), f.val = pending k outer body →
      ∃ last : ClosedNativeTerm S indexType,
        last.val = app indexType indexType (substitute (consumedArgs k outer) 0 body) t0 ∧
        StrictBetaPath S indexType k (applyRemaining S k f) last := by
  induction k with
  | zero =>
    intro outer f named
    refine ⟨applyRemaining S 0 f,?_,.nil _⟩
    exact congrArg (fun q => app indexType indexType q t0) named
  | succ k ih =>
    intro outer f named
    let a := actualArg S k
    let innerBody := bindAscending k 1 (substitute outer (k+1) body)
    have literalHead : f.val = .lam (ty (k+1)) innerBody :=
      named.trans (pendingLambda k outer body)
    have lf : ClosedNative S (.lam (ty (k+1)) innerBody)
        (.arrow (ty (k+1)) (ty (k+1))) := by
      rw [← literalHead]
      exact f.property
    obtain ⟨next,read,raw,strict⟩ :=
      NativeClosedBetaChecks.exact_ClosedNativeBeta S (ty (k+1)) (ty (k+1)) innerBody lf a
    let f' : ClosedNativeTerm S (ty (k+2)) := ⟨.lam (ty (k+1)) innerBody,lf⟩
    have same : f = f' := Subtype.ext literalHead
    have hop : BetaStep S (applyClosed f a) next := by
      rw [same]
      exact ⟨.root lf a next read,raw,strict⟩
    have namedNext : next.val = pending k (.cons a.val outer) body :=
      read.trans (pendingBeta k a.val outer body)
    obtain ⟨last,lastValue,tail⟩ := ih (.cons a.val outer) next namedNext
    have paidValue : last.val =
        app indexType indexType (substitute (consumedArgs (k+1) outer) 0 body) t0 := by
      simpa only [consumedArgs, ← actualArgLiteral S k] using lastValue
    exact ⟨last,paidValue,.cons (liftRemaining S k _ _ hop) tail⟩

private theorem beforeFixLiteral (S : Signature) (l : Nat) :
    app indexType indexType (substitute (consumedArgs (l+1) .nil) 0 (extractorFixBody l)) t0 =
      beforeFix l := by
  let values := consumedArgs (l+1) .nil
  have fixed : substitute values 0 ordinalFix = ordinalFix :=
    ClosedSyntaxProof.closedSubstitute ordinalFix (.arrow endo endo)
      (NativeOrdinalExponentialTypingProof.fixClosed S).1.1.1 values
  change app indexType indexType
    (app endo endo (substitute values 0 ordinalFix) (.lam indexType (substitute values 1 (inner l)))) t0 =
      beforeFix l
  rw [fixed] <;> rfl

theorem exact_PrintedTowerBetaPath : ExactPrintedTowerBetaPath := by
  intro S l
  let orig : ClosedNativeTerm S (ty (l+2)) := ⟨extractor l,extractorClosed S l⟩
  have head : orig.val = pending (l+1) .nil (extractorFixBody l) := by
    simp only [orig,extractor,pending,extractorFixBody,SubstitutionProof.emptySubstitution]
  obtain ⟨last,lastValue,steps⟩ := consumePending S (extractorFixBody l) (l+1) .nil orig head
  have start : applyRemaining S (l+1) orig = closedTower S (l+2) := by
    apply Subtype.ext
    rw [applyRemainingLiteral,closedTowerLiteral,exact_PrintedNativeTowerSyntax.2.2.2.2 l] <;> rfl
  rw [start] at steps
  exact ⟨last,lastValue.trans (beforeFixLiteral S l),steps⟩

#print axioms actualArgLiteral
#print axioms applyRemainingLiteral
#print axioms exact_PrintedTowerBetaPath
end LogicLineages.PersistentMarking.NativeTowerBetaPathProof
