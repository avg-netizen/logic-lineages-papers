module

public import LogicLineages.NativeModule.PersistentMarking.ProtectedSpineApplicationGapInputs

@[expose] public section

namespace LogicLineages.PersistentMarking.ProtectedSpineApplicationGapOldProof
open Spine DecisionPorts FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics
open ProtectedSpineEnvironment ProtectedSpineApplicationCounterexampleTargets ProtectedSpineApplicationGapInputs
open MarkedFamilyParameters (Parameter)

theorem bottomOutput (E : Environment) (H : List Head) (p : Parameter)
    (hp : MarkedFamilyParameters.Valid E H p) :
    StructuralActions.markedAction E H (MarkedFamilyLattice.join E H []) p =
      some (StructuralActions.bottom E p.2.1 p.2.2.1) := by
  have hf := MarkedFamilyCombineProof.combineSuccess false E H [] (by simp)
  obtain ⟨c,hc,_⟩ := StructuralMarkedActionProof.sound E H (MarkedFamilyLattice.join E H []) p hf.2.1 hp
  have hdecode := hf.2.2 p hp
  change MarkedFamilyCoding.decode E H (MarkedFamilyLattice.join E H []) p =
    MarkedFamilyLattice.aggregate false E H [] p at hdecode
  rw [StructuralMarkedActionProof.decoded E H _ p c hc] at hdecode
  have he : c = StructuralActions.bottom E p.2.1 p.2.2.1 := hdecode
  rw [← he]
  exact hc

theorem helperIsBottom (S : Signature) : helperOutput S = StructuralActions.bottom inputEnvironment .ground context := by
  let E := inputEnvironment
  let Γ := context
  let a := interpreted S argument
  let xs : List MarkedExtras.Tagged := [(.ground,a)]
  let es := MarkedExtras.down E Γ []
  let p : Parameter := (.succ,.ground,Γ,[],StructuralActions.insertExtras E Γ es xs)
  have hx : ∀ b, b ∈ xs → b ∈ MarkedExtras.«universe» E Γ := by
    intro b hb
    have he : b = (.ground,a) := by simpa [xs] using hb
    subst b
    exact (MarkedExtrasFoundationProof.universeExact E Γ .ground a).mpr ⟨groundInInventory,argumentRetained S⟩
  have hes := MarkedExtrasDownProof.downExtra E Γ [] contextValid (by simp)
  have hp : MarkedFamilyParameters.Valid E sourceHeads p :=
    ⟨List.mem_cons_self,groundInInventory,contextValid,HereditaryTupleProof.tupleNil E Γ,
      StructuralExtraInsertionProof.valid E Γ es xs contextValid hes hx⟩
  have hlookup := bottomOutput E sourceHeads p hp
  change originalHeadCall E sourceHeads bottomFamily Γ .succ (.arrow .ground .ground) [] es
    [.ground] [a] .ground = StructuralActions.bottom E .ground Γ
  unfold originalHeadCall
  rw [if_pos (show residualType (.arrow .ground .ground) [.ground] = some .ground ∧
    ([.ground] : List Ty).length = ([a] : List Code).length from ⟨rfl,rfl⟩)]
  change (StructuralActions.markedAction E sourceHeads (MarkedFamilyLattice.join E sourceHeads []) p).getD
    (StructuralActions.bottom E .ground Γ) = StructuralActions.bottom E .ground Γ
  rw [hlookup]
  rfl

theorem helperUnavailable (S : Signature) :
    (decode inputEnvironment .ground context (helperOutput S)).available context = false := by
  rw [helperIsBottom S]
  exact ((StructuralWholeBottomProof.wholeBottom inputEnvironment .ground context contextValid).2
    context contextValid (DecisionPortsProof.extensionRefl context)).1

end LogicLineages.PersistentMarking.ProtectedSpineApplicationGapOldProof
