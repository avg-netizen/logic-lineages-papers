module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowConstructorSelectionCasesProof
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowExternalLambdaComputabilityChecks
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowBindingChecks

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowConstructorFAbsCaseProof
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowSimulationData
open NumberedWindowArithmeticLeastClass NumberedWindowConstructorArgumentAddresses
open NumberedWindowConstructorOrderTargets NumberedWindowConstructorComputabilityTargets
open NumberedWindowConstructorArgumentAddressChecks NumberedWindowExternalComputability
open NumberedWindowExternalLambda NumberedWindowExternalInstance NumberedWindowExternalSubstitutionTargets
open NumberedWindowExternalLambdaComputabilityChecks
open NumberedWindowConstructorSelectionCasesProof (literalArgument)
open NumberedWindowPreservationGuardProof (lamBody)
open NumberedWindowApplicationDomainProof (rootInWindow)

private theorem listAppend (xs ys : NArgs) : (xs.append ys).toList = xs.toList ++ ys.toList := by
  cases xs with
  | nil => rfl
  | cons q rest => simp only [NArgs.append, NArgs.toList, List.cons_append, listAppend rest ys]
termination_by sizeOf xs

theorem fabs {S K Γ f σ τ k bs es} (hk : DecisionSourceUniverse.Closed K)
    (bc ec : List Nat) (hbc : Slots S K Γ bs bc) (hec : Slots S K Γ es ec)
    (hw : InWindow S K (finiteC Γ) (.arrow σ τ) (.numbered f (.arrow σ τ) (k + 1) bs es))
    (hBase : Members S K Γ hk bs) (hExtra : Members S K Γ hk es)
    (earlier : Hypothesis S K Γ hk ((Owner.numbered f (.arrow σ τ) (k + 1) bs es).measure bc ec))
    (hResult : InWindow S K (finiteC Γ) (.arrow σ τ) (.lam σ (openNumbered f σ τ k bs es))) :
    ComputableArgument S K Γ hk (.lam σ (openNumbered f σ τ k bs es)) := by
  let body : WindowCarrier S K ((finiteC Γ).push σ) τ :=
    ⟨openNumbered f σ τ k bs es, lamBody hResult⟩
  have hArrow := rootInWindow hw
  apply literalArgument hResult
  change ComputableClass S K Γ hk (.arrow σ τ) (lamClass hk hArrow (classOf body))
  apply exact_ComputableLambda S K Γ σ τ hk hArrow (classOf body)
  intro u
  refine Quot.inductionOn u ?_
  intro arg hArg
  let inst := bodyInstance hk body arg
  let newExtras := es.append (.cons arg.val .nil)
  let next : Owner := .numbered f τ k bs newExtras
  have hTerm : inst.val = next.term :=
    NumberedWindowBindingChecks.exact_OpenNumberedBeta f σ τ k bs es arg.val
  have hWindow : InWindow S K (finiteC Γ) τ next.term := hTerm ▸ inst.property
  have hNextExtras : Members S K Γ hk newExtras := by
    intro q hq
    have hm : q ∈ es.toList ++ [arg.val] := by
      simpa only [newExtras, listAppend, NArgs.toList] using hq
    rcases List.mem_append.mp hm with he | ha
    · exact hExtra q he
    · have hEq := List.mem_singleton.mp ha
      subst q
      exact literalArgument arg.property hArg
  obtain ⟨extrasCodes, hExtrasCodes, _, _⟩ :=
    exact_ComputableArgumentsGiveMultiset S K Γ hk newExtras hNextExtras
  have hHead := (NumberedWindowNumberedDomainProof.parts hw).2.2.1
  obtain ⟨rank, hRank⟩ := hHead.1
  have hEarlier : Earlier S K (next.measure bc extrasCodes)
      ((Owner.numbered f (.arrow σ τ) (k + 1) bs es).measure bc ec) :=
    .inr ⟨⟨rank, hRank, hRank⟩, .inr ⟨.rfl, .inl (Nat.lt_succ_self k)⟩⟩
  obtain ⟨_, hComputable⟩ := earlier next bc extrasCodes hbc hExtrasCodes hEarlier hWindow hBase hNextExtras
  change ComputableClass S K Γ hk τ (classOf inst)
  have hSame : inst = (⟨next.term, hWindow⟩ : WindowCarrier S K (finiteC Γ) τ) := Subtype.ext hTerm
  rw [hSame]
  exact hComputable

end LogicLineages.PersistentMarking.NumberedWindowConstructorFAbsCaseProof
