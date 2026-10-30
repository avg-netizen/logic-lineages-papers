module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowNamedDiagonalCode
public import LogicLineages.ComputabilityKnowledge.GorbowDiagonalCodeProof
public import LogicLineages.ComputabilityKnowledge.GorbowSortedNamedCodeProof
public import LogicLineages.ComputabilityKnowledge.GorbowNamedNumericCodeProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowNamedDiagonalCodeProof
open GorbowSyntax GorbowSortedSyntaxCode GorbowFreeSupport GorbowNamedBinding GorbowDiagonalSentence
open GorbowNamedDiagonalCode

theorem selectionCalibration : Comparators.GorbowNamedDiagonalCode.SelectionCalibration := by
  intro n φ v hs
  have hg := (GorbowSortedNamedCodeProof.exactNamedDomain _ _).mpr ⟨n,φ,v,rfl,rfl,hs⟩
  have hd := GorbowSortedNamedCodeProof.inputCalibration n φ v
  have hc := (GorbowNamedNumericCodeProof.originalCalibration n φ v hs).2.2.2
  unfold select
  rw [hg]
  simp only [Bool.true_eq,ite_true]
  rw [hd]
  change (GorbowNamedNumericCode.selectNumber v.val (GorbowCodeConstructors.formulaNumber φ)).bind
    (fun code => some (tagFormula code))=_
  rw [hc]
  rfl

theorem originalCalibration : Comparators.GorbowNamedDiagonalCode.OriginalCalibration := by
  intro n φ v hs
  unfold output
  rw [selectionCalibration n φ v hs]
  exact GorbowDiagonalCodeProof.calibration (selectVariable v φ)

theorem exactOutput : Comparators.GorbowNamedDiagonalCode.ExactOutput := by
  intro varCode formula out
  constructor
  · intro h
    have hg : GorbowSortedNamedCode.namedFormula varCode formula=true := by
      cases he : GorbowSortedNamedCode.namedFormula varCode formula with
      | false => simp [output,select,he] at h
      | true => rfl
    obtain ⟨n,φ,v,hv,hf,hs⟩ := (GorbowSortedNamedCodeProof.exactNamedDomain _ _).mp hg
    subst varCode
    subst formula
    rw [originalCalibration n φ v hs] at h
    exact ⟨n,φ,v,rfl,rfl,hs,(Option.some.inj h).symm⟩
  · rintro ⟨n,φ,v,rfl,rfl,hs,rfl⟩
    exact originalCalibration n φ v hs

theorem rejection : Comparators.GorbowNamedDiagonalCode.Rejection := by
  intro varCode formula
  constructor
  · intro h
    cases hg : GorbowSortedNamedCode.namedFormula varCode formula with
    | false => rfl
    | true =>
      obtain ⟨n,φ,v,rfl,rfl,hs⟩ := (GorbowSortedNamedCodeProof.exactNamedDomain _ _).mp hg
      rw [originalCalibration n φ v hs] at h
      cases h
  · intro h
    simp [output,select,h]

theorem provedOutput : Comparators.GorbowNamedDiagonalCode.ProvedOutput := by
  intro n φ v hs out h
  rw [originalCalibration n φ v hs] at h
  have he := Option.some.inj h
  subst out
  exact GorbowDiagonalSentenceProof.originalName n v φ hs

private theorem pr_mapSelect : Primrec (fun p : Nat × Nat =>
    (GorbowNamedNumericCode.selectNumber p.1 p.2).map tagFormula) :=
  Primrec.option_map GorbowNamedNumericCodeProof.uniformPrograms.2.2.2
    (GorbowSortedSyntaxCodeProof.uniformPrograms.1.comp Primrec.snd).to₂
private theorem pr_unchecked : Primrec (fun p : Nat × Nat =>
    (GorbowSortedNamedCode.decodeInputs p.1 p.2).bind
      (fun q => (GorbowNamedNumericCode.selectNumber q.1 q.2).map tagFormula)) :=
  Primrec.option_bind GorbowSortedNamedCodeProof.uniformPrograms.1
    (pr_mapSelect.comp Primrec.snd).to₂
private theorem pr_select : Primrec (fun p : Nat × Nat => select p.1 p.2) := by
  have h := Primrec.ite (Primrec.eq.comp GorbowSortedNamedCodeProof.uniformPrograms.2.1 (Primrec.const true))
    pr_unchecked (Primrec.const none)
  exact h.of_eq (fun p => by
    unfold select
    split <;> simp_all
    cases GorbowSortedNamedCode.decodeInputs p.1 p.2 <;> simp
    case some q => cases GorbowNamedNumericCode.selectNumber q.1 q.2 <;> rfl)
private theorem pr_output : Primrec (fun p : Nat × Nat => output p.1 p.2) :=
  Primrec.option_bind pr_select (GorbowDiagonalCodeProof.uniformPrograms.2.comp Primrec.snd).to₂

theorem uniformPrograms : Comparators.GorbowNamedDiagonalCode.UniformPrograms := ⟨pr_select,pr_output⟩
theorem gorbowNamedDiagonalCode : Comparators.GorbowNamedDiagonalCode.Target :=
  ⟨selectionCalibration,originalCalibration,exactOutput,rejection,provedOutput,uniformPrograms⟩
end LogicLineages.ComputabilityKnowledge.GorbowNamedDiagonalCodeProof
