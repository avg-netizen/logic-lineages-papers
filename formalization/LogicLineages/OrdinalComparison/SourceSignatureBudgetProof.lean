module
public import LogicLineages.OrdinalComparison.SourceSignatureBudgetTargets
public import LogicLineages.OrdinalComparison.ComparisonSignatureProof
public import LogicLineages.OrdinalComparison.ProfileThresholdProgramProof
public import LogicLineages.OrdinalComparison.OneVariableComparisonProgramProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.SourceSignatureBudget

theorem head_norm_budget : Targets.ActualSourceHeadNormBudget := by
  intro E
  induction E with
  | constant c => intro rho h; cases h
  | input => intro rho h; cases h
  | add E F ihE ihF =>
    intro rho h
    rcases List.mem_append.mp h with h | h
    · have hh := ihE rho h
      change Vendor.R1.treeWeight rho.1≤fixedProfileSyntaxBudget E+fixedProfileSyntaxBudget F+3
      omega
    · have hh := ihF rho h
      change Vendor.R1.treeWeight rho.1≤fixedProfileSyntaxBudget E+fixedProfileSyntaxBudget F+3
      omega
  | head rho E ih =>
    intro sigma h
    rcases List.mem_cons.mp h with h | h
    · subst sigma
      change Vendor.R1.treeWeight rho.1≤fixedProfileSyntaxBudget E+Vendor.R1.treeWeight rho.1+1
      omega
    · have hh := ih sigma h
      change Vendor.R1.treeWeight sigma.1≤fixedProfileSyntaxBudget E+Vendor.R1.treeWeight rho.1+1
      omega

private theorem word_norm_budget (w : List (NONote × Nat)) : ∀ p∈w,
    Vendor.R1.treeWeight p.1.1≤comparisonWordDomainBound w := by
  induction w with
  | nil => intro p h; cases h
  | cons q w ih =>
    intro p h
    rcases List.mem_cons.mp h with h | h
    · subst p
      change Vendor.R1.treeWeight q.1.1≤max (q.2+1+Vendor.R1.treeWeight q.1.1) (comparisonWordDomainBound w)
      omega
    · exact (ih p h).trans (Nat.le_max_right _ _)

private theorem budget_code (E : OneVariableComparisonExpr) (hv : oneVariableComparisonValid E) :
    encodedSourceSignatureBudget (oneVariableComparisonEncode E)=comparisonSourceSignatureBudget E := by
  cases E with
  | positive E =>
    have hm : (2*positiveExprEncode E)%2=0 := by omega
    have hd : (2*positiveExprEncode E)/2=positiveExprEncode E := by omega
    simpa only [encodedSourceSignatureBudget,oneVariableComparisonEncode,hm,hd,if_true,
      comparisonSourceSignatureBudget] using ProfileThresholdProgram.budget_program.2 E
  | range w E =>
    let q := Nat.pair (Encodable.encode (encodePrincipalKernelWord (comparisonRawWord w))) (positiveExprEncode E)
    have hm : (2*q+1)%2=1 := by omega
    have hd : (2*q+1)/2=q := by omega
    have hbound := (OneVariableComparison.source_program.2.2 (.range w E) hv).1
    change (if (2*q+1)%2=0 then encodedProfileSyntaxBudget ((2*q+1)/2) else
      max (encodedProfileSyntaxBudget ((2*q+1)/2).unpair.2)
        (encodedOneVariableComparisonDomainBound (oneVariableComparisonEncode (.range w E))))=_
    simp only [hm,Nat.one_ne_zero,if_false,hd,q,Nat.unpair_pair]
    rw [ProfileThresholdProgram.budget_program.2 E,hbound]
    rfl

theorem budget_program : Targets.SourceSignatureBudgetProgram := by
  have hm := Primrec.nat_mod.comp Primrec.id (Primrec.const 2)
  have hd := Primrec.nat_div.comp Primrec.id (Primrec.const 2)
  have hp := Primrec.unpair.comp hd
  have hcode : Primrec encodedSourceSignatureBudget :=
    Primrec.ite (Primrec.eq.comp hm (Primrec.const 0))
      (ProfileThresholdProgram.budget_program.1.comp hd)
      (Primrec.nat_max.comp (ProfileThresholdProgram.budget_program.1.comp (Primrec.snd.comp hp))
        OneVariableComparison.source_program.1)
  refine ⟨hcode,Primrec.nat_max.comp (hcode.comp Primrec.fst) (hcode.comp Primrec.snd),?_⟩
  intro E hv
  refine ⟨budget_code E hv,?_⟩
  cases E with
  | positive E =>
    refine ⟨(ProfileThresholdProgram.calibration E).1,head_norm_budget E,?_⟩
    intro p h
    cases h
  | range w E =>
    refine ⟨(ProfileThresholdProgram.calibration E).1.trans (Nat.le_max_left _ _),?_,?_⟩
    · intro rho h
      exact (head_norm_budget E rho h).trans (Nat.le_max_left _ _)
    · intro p h
      exact (word_norm_budget w p h).trans (Nat.le_max_right _ _)

theorem pair_carrier : Targets.SourcePairSignatureCarrier := by
  intro E F hE hF
  dsimp only
  intro G hG
  have hv : oneVariableComparisonValid G := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hG
    rcases hG with h | h
    · subst G; exact hE
    · subst G; exact hF
  have hGB : comparisonSourceSignatureBudget G≤
      encodedPairSignatureBudget (oneVariableComparisonEncode E) (oneVariableComparisonEncode F) := by
    unfold encodedPairSignatureBudget
    rw [(budget_program.2.2 E hE).1,(budget_program.2.2 F hF).1]
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hG
    rcases hG with h | h
    · subst G; exact Nat.le_max_left _ _
    · subst G; exact Nat.le_max_right _ _
  have hd := budget_program.2.2 G hv
  constructor
  · intro rho hr eta he
    exact ComparisonSignature.principal_coverage _ rho ((hd.2.2.1 rho hr).trans hGB) eta he
  · intro p hp
    exact (encodedNormalNormBallCorrect _ p.1.1).mpr ⟨p.1.2,(hd.2.2.2 p hp).trans hGB⟩

end LogicLineages.OrdinalComparison.SourceSignatureBudget
