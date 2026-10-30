module
public import LogicLineages.OrdinalComparison.LimitTailUniquenessTargets
public import LogicLineages.OrdinalComparison.HeadWindowNextProof

@[expose] public section
namespace LogicLineages.OrdinalComparison

theorem actualLimitTailUniqueness : Targets.ActualLimitTailUniqueness := by
  intro rho sigma n m hr hs heq
  have hhead : rho.1.repr=sigma.1.repr := by
    apply le_antisymm
    · by_contra h
      have hlt : sigma.1.repr<rho.1.repr := lt_of_not_ge h
      have hgap := actualLeastNextLimit sigma.1.repr rho.1.repr hr hlt
      have htail : sigma.1.repr+(m : Ordinal)<sigma.1.repr+Ordinal.omega0 :=
        add_lt_add_right (Ordinal.natCast_lt_omega0 m) _
      have hlt' : sigma.1.repr+(m : Ordinal)<rho.1.repr+(n : Ordinal) :=
        (htail.trans_le hgap).trans_le le_self_add
      exact (ne_of_lt hlt') heq.symm
    · by_contra h
      have hlt : rho.1.repr<sigma.1.repr := lt_of_not_ge h
      have hgap := actualLeastNextLimit rho.1.repr sigma.1.repr hs hlt
      have htail : rho.1.repr+(n : Ordinal)<rho.1.repr+Ordinal.omega0 :=
        add_lt_add_right (Ordinal.natCast_lt_omega0 n) _
      have hlt' : rho.1.repr+(n : Ordinal)<sigma.1.repr+(m : Ordinal) :=
        (htail.trans_le hgap).trans_le le_self_add
      exact (ne_of_lt hlt') heq
  have hnote : rho=sigma := by
    apply Subtype.ext
    letI : ONote.NF rho.1 := rho.2
    letI : ONote.NF sigma.1 := sigma.2
    exact ONote.repr_inj.mp hhead
  refine ⟨hnote,?_⟩
  rw [hhead] at heq
  have hnat : (n : Ordinal)=(m : Ordinal) := add_left_cancel heq
  exact_mod_cast hnat

end LogicLineages.OrdinalComparison
