import LogicLineages.PersistentMarking.NativeOrdinalBasisTargets
import LogicLineages.PersistentMarking.NativeClosedBetaChecks
import LogicLineages.PersistentMarking.ClosedSyntaxProof

namespace LogicLineages.PersistentMarking.NativeOrdinalCapAbstractionProof
open Spine NameBridge NativeReduction NativeCarrierTargets NativeIndexedCarrierTargets
open NativeIteratorStrictTargets NativeClosedApplication NativeOrdinalBasisTargets

/-- The literal original recursor applications before installing their base. -/
def capPrefix (B : Ty) (p : Expr) : Expr := rec2 B zero (lifted p)

/-- The original cap with its base replaced by the nearest bound variable. -/
def capBody (B : Ty) (p : Expr) : Expr := app B B (capPrefix B p) (.bound B 0)

def capAbstraction (B : Ty) (p : Expr) : Expr := .lam B (capBody B p)

private theorem prefixClosed {S B} (P : ClosedNativeTerm S (.arrow B B)) :
    ClosedNative S (capPrefix B P.val) (.arrow B B) := by
  apply NativeClosedProof.application S (stepType B) (.arrow B B)
  · exact NativeClosedProof.recOne S B
  · exact NativeClosedProof.lambda S .ground (.arrow B B) P.val P.property

theorem exact_ClosedNativeCapAbstraction {S B} (P : ClosedNativeTerm S (.arrow B B)) :
    ClosedNative S (capAbstraction B P.val) (.arrow B B) := by
  let C := EmptyContext.push B
  have head := prefixClosed P
  have bodyTyped : Typed C (capBody B P.val) B :=
    .head (.cons (ClosingProof.weakening _ _ head.1.1.1 C) (.cons (.bound rfl) .nil))
  have bodyValid : Valid S (capBody B P.val) := ⟨⟨0,rfl⟩,head.1.1.2,True.intro,True.intro⟩
  have bodyOrdinary : Ordinary (capBody B P.val) := ⟨head.1.2.1,True.intro,True.intro⟩
  refine ⟨⟨⟨.lam bodyTyped,bodyValid⟩,bodyOrdinary,?_⟩,?_⟩
  · intro n
    simpa only [capAbstraction,capBody,app,freeOccurs,freeOccursArgs,Bool.or_false] using head.1.2.2 n
  · intro n k
    simp [capAbstraction,capBody,app,DecisionInventory.heads,DecisionInventory.headsArgs,head.2 n k]

def capEndo {S B} (P : ClosedNativeTerm S (.arrow B B)) : ClosedNativeTerm S (.arrow B B) :=
  ⟨capAbstraction B P.val,exact_ClosedNativeCapAbstraction P⟩

theorem exact_NativeCapAbstractionBeta {S B} (P : ClosedNativeTerm S (.arrow B B))
    (u : ClosedNativeTerm S B) :
    substitute (.cons u.val .nil) 0 (capBody B P.val) = (cap P u).val ∧
    Reduction S (applyClosed (capEndo P) u).val (cap P u).val ∧
    NativeBelow (cap P u) (applyClosed (capEndo P) u) := by
  have literal : substitute (.cons u.val .nil) 0 (capBody B P.val) = (cap P u).val := by
    let values := Args.cons u.val .nil
    change app B B (substitute values 0 (capPrefix B P.val))
      (substitute values 0 (.bound B 0)) = app B B (capPrefix B P.val) u.val
    rw [ClosedSyntaxProof.closedSubstitute _ _ (prefixClosed P).1.1.1 values]
    simp only [values,substitute,Nat.lt_irrefl,if_false,Nat.sub_zero,Args.get,SubstitutionProof.shiftZero]
  obtain ⟨result,read,raw,strict⟩ := NativeClosedBetaChecks.exact_ClosedNativeBeta S B B
    (capBody B P.val) (exact_ClosedNativeCapAbstraction P) u
  have same : result = cap P u := Subtype.ext (read.trans literal)
  simpa only [same,capEndo,capAbstraction] using And.intro literal (And.intro raw strict)

#print axioms exact_ClosedNativeCapAbstraction
#print axioms exact_NativeCapAbstractionBeta

end LogicLineages.PersistentMarking.NativeOrdinalCapAbstractionProof
