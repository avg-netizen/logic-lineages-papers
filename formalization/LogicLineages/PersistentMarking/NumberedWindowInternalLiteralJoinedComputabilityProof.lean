module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralConcreteJoinedApplicationRulesProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFreshNeutralBridgeProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJoinedComputabilityProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAccessibilityRules (membership)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalFreshProbeParsedTyped (Inputs chosenH chosenA)
open NumberedWindowInternalLiteralFiniteScalarGuardProof (finiteCodes)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy ValidWindow)
open NumberedWindowRawExchangeSymmetryTargets (HeadPairsSymmetric)
open NumberedWindowInternalLiteralCoveredMemo (WindowSeedsCovered)
open NumberedWindowInternalSettingsGrammarGuardNumericTargets (GrammarTypeInclusion)
open NumberedWindowInternalLiteralDirectCarrierInstalledProof (Packet)
open NumberedWindowInternalLiteralHopCarrier (rawWithTarget)
open NumberedWindowInternalLiteralAddressedChildReportsProof (S hop)
open NumberedWindowInternalSparseApplicationFrontend (applicationGuard applicationCore)
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalNeutralFactsTargets (D Arithmetic FactsAt)
open NumberedWindowInternalNeutralFactsProof (exact_ConditionalInternalNeutralFacts)
open NumberedWindowInternalLiteralFreshNeutralBridgeProof
  (exact_LiteralFreshFromNeutral exact_TupleComputabilityToIFromArithmetic)
open NumberedWindowInternalLiteralNeutralAtomProof (neutralSource)
open NumberedWindowInternalAtomicRefinement (bottomSource freeSource)
open NumberedWindowInternalLiteralConcreteJoinedApplicationRulesProof (exact_ConcreteJoinedApplicationRules)
open NumberedWindowInternalProbeTargets (FreshVariablesComputable typedAt)
open NumberedWindowInternalPullbackTargets (ForwardRule Pullback)
open NumberedWindowComputabilityFormulaTargets (formula)

/-- All open computability conclusions for one original installed tuple. -/
def JoinedComputabilityAt (xs : Entries) (s : Settings) (P : List ProbeTy) : Prop :=
    ∃ (i cv tv : Program 1) (raw : Program 5) (L : Program 3) (v : Inputs),
      Packet xs s P i cv tv raw L (applicationCore L) v ∧
      v.applicationGuard = applicationGuard i L ∧
      (∀ c : Nat, let R := rawWithTarget i cv tv raw L
        let data := S i cv tv R L
        let h := hop cv tv R L
        Arithmetic data v.applicationGuard h neutralSource bottomSource freeSource c ∧
        ForwardRule data v.applicationGuard c ∧ Pullback data v.applicationGuard c ∧
        FreshVariablesComputable data v.applicationGuard (chosenH v P) (chosenA v) c ∧
        (∀ τ : LogicLineages.OrdinalComparison.Source.Ty,
          FactsAt data v.applicationGuard h neutralSource bottomSource freeSource c τ ∧
          ∀ (α : Type) (Γ : List (Formula α)) (q : OTerm α),
            D data c Γ (typedAt (chosenH v P) τ q) →
            D data c Γ (formula v.applicationGuard τ q) →
            D data c Γ (membership false q)))

/-- The actual single calibrated checker proves arrow-type neutral,
bottom, variable and fresh-variable computability, and sends every
typed computability derivation to original scalar membership. No
computability premise for arbitrary terms is discharged by this theorem. -/
theorem exact_ConcreteJoinedComputability (xs : Entries) (s : Settings) (P : List ProbeTy)
    (valid : ValidWindow s P) (seeds : WindowSeedsCovered s) (symmetric : HeadPairsSymmetric s.equivalentHeads)
    (grammar : GrammarTypeInclusion s) (included : ∀ n ∈ finiteCodes P, n ∈ s.window.1) :
    JoinedComputabilityAt xs s P := by
  obtain ⟨i,cv,tv,raw,L,v,packet,same,joined⟩ :=
    exact_ConcreteJoinedApplicationRules xs s P valid seeds symmetric grammar included
  refine ⟨i,cv,tv,raw,L,v,packet,same,?_⟩
  intro c R data h
  obtain ⟨_,arith,forward,pull,_⟩ := joined c
  rw [← same] at arith forward pull
  let r := addressPositive cv tv R L
  let d := dCore i r permutation
  have tuple := packet.physical.1
  obtain ⟨_,_,_,_,_,_,_,_,_,shape,aligned⟩ := tuple
  have fresh := exact_LiteralFreshFromNeutral v P data h neutralSource bottomSource c shape (aligned c) arith
  refine ⟨arith,forward,pull,fresh,fun τ => ⟨exact_ConditionalInternalNeutralFacts arith τ,?_⟩⟩
  intro α Γ q typed computed
  exact exact_TupleComputabilityToIFromArithmetic xs s P i (jRaw i) r d v c
    h neutralSource bottomSource packet.physical.1 arith forward τ α Γ q typed computed

#print axioms JoinedComputabilityAt
#print axioms exact_ConcreteJoinedComputability
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJoinedComputabilityProof
