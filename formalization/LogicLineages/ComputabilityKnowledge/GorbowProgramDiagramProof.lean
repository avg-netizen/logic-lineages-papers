module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowProgramDiagram
public import LogicLineages.ComputabilityKnowledge.GorbowRegistryDiagramProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowProgramDiagramProof
open GorbowSyntax GorbowTheoryProof GorbowSortedRevision GorbowProgramDiagram
open GorbowRegistryDiagram (relationSentence functionSentence equationArgs)
open GorbowRegistryDiagramProof (equationArgsExact)
open GorbowCodeConstructors (numeral)

variable (R : Nat → Bool) (F : Nat → Nat)

private theorem positiveProgram (n : Nat) : axiomProgram R F (1::numeral n)=R n := by
  have hn := (GorbowNumeralPrefixCodeProof.closedExact _ n).mpr rfl
  simp [axiomProgram,hn]
private theorem negativeProgram (n : Nat) : axiomProgram R F (6::1::numeral n)= !(R n) := by
  have hn := (GorbowNumeralPrefixCodeProof.closedExact _ n).mpr rfl
  simp [axiomProgram,hn]
private theorem functionProgram (n m : Nat) : axiomProgram R F (0::5::(numeral n++numeral m))=
    decide (F n=m) := by
  have hn := (equationArgsExact _ n m).mpr rfl
  simp [axiomProgram,hn]

private theorem programCases (raw : List Nat) : axiomProgram R F raw=true ↔
    (∃ n,raw=1::numeral n ∧ R n=true) ∨
    (∃ n,raw=6::1::numeral n ∧ R n=false) ∨
    (∃ n m,raw=0::5::(numeral n++numeral m) ∧ F n=m) := by
  constructor
  · intro h
    unfold axiomProgram at h
    split at h
    · rename_i hs
      cases hn : GorbowNumeralPrefixCode.decode raw.tail with
      | none => simp [hn] at h
      | some n =>
        have he : raw.drop 1=numeral n := by simpa using (GorbowNumeralPrefixCodeProof.closedExact _ n).mp hn
        refine Or.inl ⟨n,?_,by simpa [hn] using h⟩
        calc raw=raw.take 1++raw.drop 1 := (List.take_append_drop 1 raw).symm
             _=1::numeral n := by rw [hs,he]; rfl
    · split at h
      · rename_i hs
        cases hn : GorbowNumeralPrefixCode.decode (raw.drop 2) with
        | none => simp [hn] at h
        | some n =>
          have he := (GorbowNumeralPrefixCodeProof.closedExact _ n).mp hn
          refine Or.inr (Or.inl ⟨n,?_,by simpa [hn] using h⟩)
          calc raw=raw.take 2++raw.drop 2 := (List.take_append_drop 2 raw).symm
               _=6::1::numeral n := by rw [hs,he]; rfl
      · split at h
        · rename_i hs
          cases hn : equationArgs (raw.drop 2) with
          | none => simp [hn] at h
          | some p =>
            rcases p with ⟨n,m⟩
            have he := (equationArgsExact _ n m).mp hn
            refine Or.inr (Or.inr ⟨n,m,?_,by simpa [hn] using h⟩)
            calc raw=raw.take 2++raw.drop 2 := (List.take_append_drop 2 raw).symm
                 _=0::5::(numeral n++numeral m) := by rw [hs,he]; rfl
        · contradiction
  · rintro (⟨n,rfl,h⟩|⟨n,rfl,h⟩|⟨n,m,rfl,h⟩)
    · simpa [positiveProgram] using h
    · simp [negativeProgram,h]
    · simp [functionProgram,h]

private theorem relationEncoding (n : Nat) : GorbowFormulaPrefixCode.encode (relationSentence n)=1::numeral n := by
  simp only [relationSentence,GorbowFormulaPrefixCode.encode]
  rw [GorbowCodeConstructorsProof.numeralCalibration 0 n]
private theorem functionEncoding (n m : Nat) : GorbowFormulaPrefixCode.encode (functionSentence n m)=0::5::(numeral n++numeral m) := by
  simp only [functionSentence,GorbowFormulaPrefixCode.encode,GorbowTermPrefixCode.encode,List.cons_append]
  rw [GorbowCodeConstructorsProof.numeralCalibration 0 n,GorbowCodeConstructorsProof.numeralCalibration 0 m]

theorem exactProgram : Comparators.GorbowProgramDiagram.ExactProgram := by
  intro R F raw
  rw [programCases]
  constructor
  · rintro (⟨n,hr,h⟩|⟨n,hr,h⟩|⟨n,m,hr,h⟩)
    · exact ⟨relationSentence n,hr.trans (relationEncoding n).symm,.positive n h⟩
    · refine ⟨.neg (relationSentence n),?_,.negative n h⟩
      simpa only [GorbowFormulaPrefixCode.encode,relationEncoding] using hr
    · subst m
      exact ⟨functionSentence n (F n),hr.trans (functionEncoding _ _).symm,.functionValue n⟩
  · rintro ⟨σ,rfl,h⟩
    cases h with
    | positive n h => exact Or.inl ⟨n,relationEncoding n,h⟩
    | negative n h => exact Or.inr (Or.inl ⟨n,by simp only [GorbowFormulaPrefixCode.encode,relationEncoding],h⟩)
    | functionValue n => exact Or.inr (Or.inr ⟨n,_,functionEncoding _ _,rfl⟩)

theorem actualTheory : Comparators.GorbowProgramDiagram.ActualTheory := by
  intro R F σ
  change axiomProgram R F (GorbowFormulaPrefixCode.encode σ)=true ↔ _
  rw [exactProgram]
  constructor
  · rintro ⟨τ,he,hτ⟩
    have h := GorbowFormulaPrefixCodeProof.encodingInjective 0 he
    subst τ
    exact hτ
  · intro h; exact ⟨σ,rfl,h⟩

theorem diagramSoundness : Comparators.GorbowProgramDiagram.DiagramSoundness := by
  intro R F P σ h
  cases h with
  | positive n h =>
    simpa [relationSentence,Formula.realize,Term.realize,numeral_realize,interpretation,GorbowRevisionSemantics.interpretation,ground,ground] using h
  | negative n h =>
    change ¬ (R ((Term.numeral n).realize _ Fin.elim0)=true)
    simp [numeral_realize,h]
  | functionValue n =>
    simp [functionSentence,Formula.realize,Term.realize,numeral_realize,interpretation,GorbowRevisionSemantics.interpretation,ground]

theorem theorySoundness : Comparators.GorbowProgramDiagram.TheorySoundness := by
  intro R F P n φ p
  exact GorbowTheoryProofProof.theorySoundness (Theory R F) n φ p _
    (fun σ h => diagramSoundness R F P σ ((actualTheory R F σ).mp h))

private theorem closedAxiom (σ : Sentence) (h : DiagramAxiom R F σ) : Nonempty (Derivation (Theory R F) σ) := by
  have p := Derivation.axiom (A:=(Theory R F)) (n:=0) σ ((actualTheory R F σ).mpr h)
  simpa only [GorbowClosedDeductionProof.closedSyntax.1] using (show Nonempty (Derivation (Theory R F) (weakenClosed 0 σ)) from ⟨p⟩)

theorem numeralwiseRepresentation : Comparators.GorbowProgramDiagram.NumeralwiseRepresentation := by
  intro R F
  refine ⟨?_,?_,?_⟩
  · intro n
    constructor
    · rintro ⟨p⟩
      have h := theorySoundness R F (fun _ => False) 0 _ p Fin.elim0
      simpa [relationSentence,Formula.realize,numeral_realize,interpretation,GorbowRevisionSemantics.interpretation,ground,ground] using h
    · intro h; exact closedAxiom R F _ (.positive n h)
  · intro n
    constructor
    · rintro ⟨p⟩
      have h := theorySoundness R F (fun _ => False) 0 _ p Fin.elim0
      simpa [relationSentence,Formula.realize,numeral_realize,interpretation,GorbowRevisionSemantics.interpretation,ground,ground] using h
    · intro h; exact closedAxiom R F _ (.negative n h)
  · intro n m
    constructor
    · rintro ⟨p⟩
      have h := theorySoundness R F (fun _ => False) 0 _ p Fin.elim0
      simpa [functionSentence,Formula.realize,Term.realize,numeral_realize,interpretation,GorbowRevisionSemantics.interpretation,ground,ground] using h
    · intro h; subst m; exact closedAxiom R F _ (.functionValue n)

theorem diagramConsistency : Comparators.GorbowProgramDiagram.DiagramConsistency := by
  intro R F
  rintro ⟨p⟩
  exact falseEquality_not_realized _ (theorySoundness R F (fun _ => False) 0 _ p Fin.elim0)


private theorem pr_relation (hR : Primrec R) (positive : Bool) : Primrec (fun raw : List Nat =>
    ((GorbowNumeralPrefixCode.decode raw).map (fun n => if positive then R n else !(R n))).getD false) := by
  have hv : Primrec (fun p : List Nat × Nat => if positive then R p.2 else !(R p.2)) := by
    cases positive with
    | false => exact Primrec.not.comp (hR.comp Primrec.snd)
    | true => exact hR.comp Primrec.snd
  exact Primrec.option_getD.comp (Primrec.option_map GorbowNumeralPrefixCodeProof.uniformPrograms.2.2 hv.to₂) (Primrec.const false)
private theorem pr_function (hF : Primrec F) : Primrec (fun raw : List Nat =>
    ((equationArgs raw).map (fun p => decide (F p.1=p.2))).getD false) := by
  have hv : Primrec (fun p : List Nat × (Nat × Nat) => decide (F p.2.1=p.2.2)) :=
    (Primrec.eq.comp (hF.comp (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd)).decide
  exact Primrec.option_getD.comp (Primrec.option_map GorbowRegistryDiagramProof.uniformPrograms.1 hv.to₂) (Primrec.const false)

theorem uniformProgram : Comparators.GorbowProgramDiagram.UniformProgram := by
  intro R F hR hF
  have hd (n : Nat) : Primrec (fun raw : List Nat => raw.drop n) := Primrec.list_drop.comp (Primrec.const n) Primrec.id
  have ht (n : Nat) (pref : List Nat) : PrimrecPred (fun raw : List Nat => raw.take n=pref) :=
    Primrec.eq.comp (Primrec.list_take.comp (Primrec.const n) Primrec.id) (Primrec.const pref)
  have h := Primrec.ite (ht 1 [1]) ((pr_relation R hR true).comp (hd 1))
    (Primrec.ite (ht 2 [6,1]) ((pr_relation R hR false).comp (hd 2))
      (Primrec.ite (ht 2 [0,5]) ((pr_function F hF).comp (hd 2)) (Primrec.const false)))
  exact h.of_eq (fun raw => by simp [axiomProgram])

theorem gorbowProgramDiagram : Comparators.GorbowProgramDiagram.Target :=
  ⟨exactProgram,actualTheory,diagramSoundness,theorySoundness,numeralwiseRepresentation,diagramConsistency,uniformProgram⟩
end LogicLineages.ComputabilityKnowledge.GorbowProgramDiagramProof
