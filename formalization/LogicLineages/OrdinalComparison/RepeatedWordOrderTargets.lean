module
public import LogicLineages.OrdinalComparison.RepeatedWordOrderDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-! Finite child-word comparisons for paper07 strict mass. The final target is
an explicitly local induction-step supplier, never the full source theorem;
its child strictness hypothesis must be discharged by the final induction. -/
def ActualRepeatedWordWeakOrder : Prop :=
  ∀ eta : NONote, 0 < eta.1.repr → ∀ q c e U V : Nat,
    c ≤ e → e+q*actualOrdinalNorm (Ordinal.omega0^eta.1.repr) ≤ U → U ≤ V →
      (actualPrincipalWordRun (principalKernelWord (List.replicate q eta.1) e) U).1 ≤
        (actualPrincipalWordRun (principalKernelWord (List.replicate q eta.1) c) V).1

def ActualRepeatedWordStrictInput : Prop :=
  ∀ eta : NONote, 0 < eta.1.repr → ∀ q c e U V : Nat,
    c ≤ e → e+q*actualOrdinalNorm (Ordinal.omega0^eta.1.repr) ≤ U → U < V →
      (actualPrincipalWordRun (principalKernelWord (List.replicate q eta.1) e) U).1 <
        (actualPrincipalWordRun (principalKernelWord (List.replicate q eta.1) c) V).1

def ActualRepeatedWordStrictMass : Prop :=
  ∀ eta : NONote, 0 < eta.1.repr → ∀ S : Nat,
    ((Ordinal.omega0^eta.1.repr = Ordinal.omega0^(2 : Ordinal) ∧ S=0) ∨
      (Ordinal.omega0^(3 : Ordinal) ≤ Ordinal.omega0^eta.1.repr ∧
        actualKernelStrictMassAt (Ordinal.omega0^eta.1.repr) S)) →
    ∀ q c e U V : Nat, 2 ≤ q → c < e → S ≤ U →
      e+q*actualOrdinalNorm (Ordinal.omega0^eta.1.repr) ≤ U → U ≤ V →
      (actualPrincipalWordRun (principalKernelWord (List.replicate q eta.1) e) U).1 <
        (actualPrincipalWordRun (principalKernelWord (List.replicate q eta.1) c) V).1

end LogicLineages.OrdinalComparison.Targets
