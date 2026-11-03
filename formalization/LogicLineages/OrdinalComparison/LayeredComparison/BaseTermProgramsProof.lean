module
public import LogicLineages.OrdinalComparison.LayeredComparison.BaseTermProgramsTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BaseTermPrograms.Proof
open CommonLayerSyntax

private theorem decode_zero (n:Nat) (h:n%4=0):BaseTerm.decode n=.numeral (n/4):=by
  rw [BaseTerm.decode,dif_pos h]
private theorem decode_variable (n:Nat) (h:n%4=1):BaseTerm.decode n=.variable (n/4):=by
  have h0:n%4≠0:=by omega
  rw [BaseTerm.decode,dif_neg h0,dif_pos h]
private theorem decode_add (n:Nat) (h:n%4=2):BaseTerm.decode n=
    .add (BaseTerm.decode (n/4).unpair.1) (BaseTerm.decode (n/4).unpair.2):=by
  have h0:n%4≠0:=by omega
  have h1:n%4≠1:=by omega
  rw [BaseTerm.decode,dif_neg h0,dif_neg h1,dif_pos h]
private theorem decode_phi (n:Nat) (h:n%4=3):BaseTerm.decode n=.phi (BaseTerm.decode (n/4)):=by
  have h0:n%4≠0:=by omega
  have h1:n%4≠1:=by omega
  have h2:n%4≠2:=by omega
  rw [BaseTerm.decode,dif_neg h0,dif_neg h1,dif_neg h2]

theorem finiteCallEquation:Targets.FiniteCallEquation:=by
  constructor
  · intro p q hq
    rcases p with ⟨n,table⟩
    by_cases h2:n%4=2
    · have hpos:0<n:=by omega
      have hd:n/4<n:=Nat.div_lt_self hpos (by decide)
      have hl:(n/4).unpair.1<n:=lt_of_le_of_lt (Nat.unpair_left_le _) hd
      have hr:(n/4).unpair.2<n:=lt_of_le_of_lt (Nat.unpair_right_le _) hd
      simp only [children,if_pos h2,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hq
      rcases hq with he|he
      · subst q;exact hl
      · subst q;exact hr
    · by_cases h3:n%4=3
      · have hpos:0<n:=by omega
        have hd:n/4<n:=Nat.div_lt_self hpos (by decide)
        simp only [children,if_neg h2,if_pos h3,List.mem_singleton] at hq
        subst q
        exact hd
      · simp only [children,if_neg h2,if_neg h3,List.not_mem_nil] at hq
  · intro p
    rcases p with ⟨n,table⟩
    have hr:n%4<4:=Nat.mod_lt _ (by decide)
    by_cases h0:n%4=0
    · have h2:n%4≠2:=by omega
      have h3:n%4≠3:=by omega
      simp [joint,valueCode,variablesCode,decode_zero n h0,BaseTerm.value,BaseTerm.variables,
        children,assemble,h0,h2,h3]
    by_cases h1:n%4=1
    · have h2:n%4≠2:=by omega
      have h3:n%4≠3:=by omega
      simp [joint,valueCode,variablesCode,decode_variable n h1,BaseTerm.value,BaseTerm.variables,
        children,assemble,h0,h1,h2,h3]
    by_cases h2:n%4=2
    · simp [joint,valueCode,variablesCode,decode_add n h2,BaseTerm.value,BaseTerm.variables,
        children,assemble,h0,h1,h2]
    · have h3:n%4=3:=by omega
      simp [joint,valueCode,variablesCode,decode_phi n h3,BaseTerm.value,BaseTerm.variables,
        children,assemble,h0,h1,h2,h3]

theorem supportStability:Targets.SupportStability:=by
  intro E
  induction E with
  | numeral n=>intro ν μ h;rfl
  | «variable» i=>
    intro ν μ h
    exact h i (by simp [BaseTerm.variables])
  | add E F ihE ihF=>
    intro ν μ h
    exact congrArg₂ Nat.add
      (ihE ν μ (fun i hi=>h i (List.mem_append_left _ hi)))
      (ihF ν μ (fun i hi=>h i (List.mem_append_right _ hi)))
  | phi E ih=>
    intro ν μ h
    exact congrArg Phi (ih ν μ h)

theorem supportDomination:Targets.SupportDomination:=by
  intro E
  induction E with
  | numeral n=>intro ν i h;cases h
  | «variable» j=>
    intro ν i h
    simp only [BaseTerm.variables,List.mem_singleton] at h
    subst i
    exact le_rfl
  | add E F ihE ihF=>
    intro ν i h
    rcases List.mem_append.mp h with he|hf
    · have hh:=ihE ν i he
      change ν i≤E.value ν+F.value ν
      omega
    · have hh:=ihF ν i hf
      change ν i≤E.value ν+F.value ν
      omega
  | phi E ih=>
    intro ν i h
    exact (ih ν i h).trans (self_lt_Phi _).le
end LogicLineages.OrdinalComparison.LayeredComparison.BaseTermPrograms.Proof
