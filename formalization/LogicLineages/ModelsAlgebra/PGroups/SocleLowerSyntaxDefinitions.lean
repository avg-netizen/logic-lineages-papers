module
public import LogicLineages.ModelsAlgebra.PGroups.UlmLowerFormulaDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.AdaptedSocleDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
open GroupBackAndForth
open scoped BigOperators

def socleRootTerm (p j n m:ℕ) (i:Fin m) : GroupTerm (n+m) :=
  multipleTerm (p^j) (.var (Fin.natAdd n i))
def socleCombinationTerm (p j n m:ℕ) (r:Fin m→ZMod p) : GroupTerm (n+m) :=
  finiteSumTerm m (fun i=>multipleTerm (r i).val (socleRootTerm p j n m i))
noncomputable def socleLowerMatrix (p:ℕ) [Fact p.Prime] (j n m:ℕ) : QF (n+m) := by
  classical
  let coeff := (Fintype.equivFin (Fin m→ZMod p)).symm
  exact .and
    (finiteAnd m (fun i=>.equal (multipleTerm p (socleRootTerm p j n m i)) .zero))
    (finiteAnd (Fintype.card (Fin m→ZMod p)) (fun k=>
      if coeff k=0 then .neg .falsum else .neg (.equal (socleCombinationTerm p j n m (coeff k)) .zero)))
noncomputable def socleLowerFormula (p:ℕ) [Fact p.Prime] (j n m:ℕ) : Formula n :=
  .disjEx {0} (fun _=>m) (fun _=>.qf (socleLowerMatrix p j n m))
def SocleRootWitnesses {G:Type} [AddCommGroup G] (p j:ℕ) {m:ℕ} (d:Fin m→G) : Prop :=
  (∀i,p • (p^j • d i)=0) ∧
    ∀ r:Fin m→ZMod p, r≠0 → (∑ i,(r i).val • (p^j • d i))≠0
end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
