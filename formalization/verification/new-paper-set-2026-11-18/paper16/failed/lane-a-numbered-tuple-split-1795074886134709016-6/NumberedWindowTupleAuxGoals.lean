import LogicLineages.PersistentMarking.NumberedWindowTupleBridgeProof

namespace LogicLineages.PersistentMarking.NumberedWindowTupleAuxGoals
open Spine NumberedWindowSyntax NumberedWindowDomain NumberedWindowRules NumberedWindowTupleTargets
open NumberedWindowSourceGuardTargets NumberedWindowTupleBridgeProof

/-- The stopped proof's generalized predicate, regrouped so an induction
hypothesis can be passed to just the original lambda constructor case. -/
def AtArgs (S : Signature) (K : List Ty) (C : BoundContext) (n B : Nat)
    (args : Spine.Args) (q : Expr) : Prop :=
  ∀ (values : Spine.Args) (types : List Ty) (σ τ : Ty) (r : Expr)
    (Q : NTerm) (As Vs : NArgs),
    DecisionSourceUniverse.Closed K → n + args.length + 1 ≤ B →
    SourceGuard S K (BoundContext.prefix types C) σ q →
    SourceValues S K C types values → CallTyped C σ args τ →
    ValidArgs S args → SymbolicArgsAdmissible K args →
    Spine.applyAux q args values = some r →
    Realizes B q Q → RealizesArgs B args As → RealizesArgs B values Vs →
    Conclusion S K C n τ (NumberedWindowSyntax.substitute Vs 0 Q) As r

def ForArgs (S : Signature) (K : List Ty) (C : BoundContext) (n B : Nat) (args : Spine.Args) : Prop :=
  ∀ q, AtArgs S K C n B args q

theorem substituteWindow {S : Signature} {K : List Ty} {C : BoundContext}
    {types : List Ty} {σ : Ty} {B : Nat} {q : Expr} {values : Spine.Args}
    {Q : NTerm} {Vs : NArgs}
    (hQ : SourceGuard S K (BoundContext.prefix types C) σ q)
    (hValues : SourceValues S K C types values)
    (hRep : Realizes B q Q) (hVs : RealizesArgs B values Vs) :
    InWindow S K C σ (NumberedWindowSyntax.substitute Vs 0 Q) := by
  have hW := NumberedWindowSourceGuardChecks.exact_ActualBlockGuard S K C types values q σ hQ hValues
  exact NumberedWindowRealizationChecks.exact_RealizationInWindow S K C σ B _ _
    hW.1 hW.2.1 hW.2.2 (NumberedWindowRealizationSubstitutionProof.term hVs hRep 0)

theorem nilCase (S : Signature) (K : List Ty) (C : BoundContext) (n B : Nat) (q : Expr) :
    AtArgs S K C n B .nil q := by
  intro values types σ τ r Q As Vs hk hBudget hW hValues hCall hv hu hr hRep hAs hVs
  have hn : n ≤ B := by omega
  have hNum := substituteWindow hW hValues hRep hVs
  have hRep' := NumberedWindowRealizationSubstitutionProof.term hVs hRep 0
  cases hCall
  cases hAs
  simp only [Spine.applyAux,Option.some.injEq] at hr
  subst r
  exact ⟨_,_,rfl,.refl hNum,NumberedWindowRealizationShapeProof.weakensTerm hn hRep'⟩

end LogicLineages.PersistentMarking.NumberedWindowTupleAuxGoals
