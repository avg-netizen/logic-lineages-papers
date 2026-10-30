module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowRegistryDiagram
public import LogicLineages.ComputabilityKnowledge.GorbowNumeralPrefixCodeProof
public import LogicLineages.ComputabilityKnowledge.GorbowAtomicRegistryProof
public import LogicLineages.ComputabilityKnowledge.GorbowClosedDeductionProof
public import LogicLineages.ComputabilityKnowledge.GorbowTheoryProofProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowRegistryDiagramProof
open GorbowSyntax GorbowTheoryProof GorbowSortedRevision GorbowRegistryDiagram
open GorbowCodeConstructors (numeral)

theorem equationArgsExact : Comparators.GorbowRegistryDiagram.EquationArgsExact := by
  intro raw n m
  constructor
  · intro h
    cases hp : GorbowNumeralPrefixCode.parse raw with
    | none => simp [equationArgs,hp] at h
    | some p =>
      rcases p with ⟨j,rest⟩
      cases hm : GorbowNumeralPrefixCode.decode rest with
      | none => simp [equationArgs,hp,hm] at h
      | some k =>
        have he : (j,k)=(n,m) := by simpa [equationArgs,hp,hm] using h
        cases he
        rw [(GorbowNumeralPrefixCodeProof.prefixExact raw _ rest).mp hp,
          (GorbowNumeralPrefixCodeProof.closedExact rest _).mp hm]
  · intro h
    subst raw
    have hp := (GorbowNumeralPrefixCodeProof.prefixExact _ n (numeral m)).mpr rfl
    have hm := (GorbowNumeralPrefixCodeProof.closedExact _ m).mpr rfl
    simp [equationArgs,hp,hm]

private theorem positiveProgram (n : Nat) : axiomProgram (1::numeral n)=GorbowSortedRegistry.relationProgram n := by
  have hn := (GorbowNumeralPrefixCodeProof.closedExact _ n).mpr rfl
  simp [axiomProgram,hn]
private theorem negativeProgram (n : Nat) : axiomProgram (6::1::numeral n)= !(GorbowSortedRegistry.relationProgram n) := by
  have hn := (GorbowNumeralPrefixCodeProof.closedExact _ n).mpr rfl
  simp [axiomProgram,hn]
private theorem functionProgram (n m : Nat) : axiomProgram (0::5::(numeral n++numeral m))=
    decide (GorbowAtomicRegistry.functionProgram n=m) := by
  have hn := (equationArgsExact _ n m).mpr rfl
  simp [axiomProgram,hn]

private theorem programCases (raw : List Nat) : axiomProgram raw=true ↔
    (∃ n,raw=1::numeral n ∧ GorbowSortedRegistry.relationProgram n=true) ∨
    (∃ n,raw=6::1::numeral n ∧ GorbowSortedRegistry.relationProgram n=false) ∨
    (∃ n m,raw=0::5::(numeral n++numeral m) ∧ GorbowAtomicRegistry.functionProgram n=m) := by
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

theorem exactProgram : Comparators.GorbowRegistryDiagram.ExactProgram := by
  intro raw
  rw [programCases]
  constructor
  · rintro (⟨n,hr,h⟩|⟨n,hr,h⟩|⟨n,m,hr,h⟩)
    · exact ⟨relationSentence n,hr.trans (relationEncoding n).symm,.positive n h⟩
    · refine ⟨.neg (relationSentence n),?_,.negative n h⟩
      simpa only [GorbowFormulaPrefixCode.encode,relationEncoding] using hr
    · subst m
      exact ⟨functionSentence n (GorbowAtomicRegistry.functionProgram n),hr.trans (functionEncoding _ _).symm,.functionValue n⟩
  · rintro ⟨σ,rfl,h⟩
    cases h with
    | positive n h => exact Or.inl ⟨n,relationEncoding n,h⟩
    | negative n h => exact Or.inr (Or.inl ⟨n,by simp only [GorbowFormulaPrefixCode.encode,relationEncoding],h⟩)
    | functionValue n => exact Or.inr (Or.inr ⟨n,_,functionEncoding _ _,rfl⟩)

theorem actualTheory : Comparators.GorbowRegistryDiagram.ActualTheory := by
  intro σ
  change axiomProgram (GorbowFormulaPrefixCode.encode σ)=true ↔ _
  rw [exactProgram]
  constructor
  · rintro ⟨τ,he,hτ⟩
    have h := GorbowFormulaPrefixCodeProof.encodingInjective 0 he
    subst τ
    exact hτ
  · intro h; exact ⟨σ,rfl,h⟩

theorem diagramSoundness : Comparators.GorbowRegistryDiagram.DiagramSoundness := by
  intro P σ h
  cases h with
  | positive n h =>
    simpa [relationSentence,Formula.realize,Term.realize,numeral_realize,interpretation,GorbowRevisionSemantics.interpretation,GorbowAtomicRegistry.ground,GorbowSortedRegistry.ground] using h
  | negative n h =>
    change ¬ (GorbowSortedRegistry.relationProgram ((Term.numeral n).realize _ Fin.elim0)=true)
    simp [numeral_realize,h]
  | functionValue n =>
    simp [functionSentence,Formula.realize,Term.realize,numeral_realize,interpretation,GorbowRevisionSemantics.interpretation,GorbowAtomicRegistry.ground]

theorem theorySoundness : Comparators.GorbowRegistryDiagram.TheorySoundness := by
  intro P n φ p
  exact GorbowTheoryProofProof.theorySoundness Theory n φ p _
    (fun σ h => diagramSoundness P σ ((actualTheory σ).mp h))

private theorem closedAxiom (σ : Sentence) (h : DiagramAxiom σ) : Nonempty (Derivation Theory σ) := by
  have p := Derivation.axiom (A:=Theory) (n:=0) σ ((actualTheory σ).mpr h)
  simpa only [GorbowClosedDeductionProof.closedSyntax.1] using (show Nonempty (Derivation Theory (weakenClosed 0 σ)) from ⟨p⟩)

theorem numeralwiseRepresentation : Comparators.GorbowRegistryDiagram.NumeralwiseRepresentation := by
  refine ⟨?_,?_,?_⟩
  · intro n
    constructor
    · rintro ⟨p⟩
      have h := theorySoundness (fun _ => False) 0 _ p Fin.elim0
      simpa [relationSentence,Formula.realize,numeral_realize,interpretation,GorbowRevisionSemantics.interpretation,GorbowAtomicRegistry.ground,GorbowSortedRegistry.ground] using h
    · intro h; exact closedAxiom _ (.positive n h)
  · intro n
    constructor
    · rintro ⟨p⟩
      have h := theorySoundness (fun _ => False) 0 _ p Fin.elim0
      simpa [relationSentence,Formula.realize,numeral_realize,interpretation,GorbowRevisionSemantics.interpretation,GorbowAtomicRegistry.ground,GorbowSortedRegistry.ground] using h
    · intro h; exact closedAxiom _ (.negative n h)
  · intro n m
    constructor
    · rintro ⟨p⟩
      have h := theorySoundness (fun _ => False) 0 _ p Fin.elim0
      simpa [functionSentence,Formula.realize,Term.realize,numeral_realize,interpretation,GorbowRevisionSemantics.interpretation,GorbowAtomicRegistry.ground,GorbowSortedRegistry.ground] using h
    · intro h; subst m; exact closedAxiom _ (.functionValue n)

theorem diagramConsistency : Comparators.GorbowRegistryDiagram.DiagramConsistency := by
  rintro ⟨p⟩
  exact falseEquality_not_realized _ (theorySoundness (fun _ => False) 0 _ p Fin.elim0)

private theorem pr_eqInner : Primrec (fun p : List Nat × (Nat × List Nat) =>
    (GorbowNumeralPrefixCode.decode p.2.2).map (fun m => (p.2.1,m))) :=
  Primrec.option_map (GorbowNumeralPrefixCodeProof.uniformPrograms.2.2.comp (Primrec.snd.comp Primrec.snd))
    ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair Primrec.snd).to₂
private theorem pr_equationArgs : Primrec equationArgs := by
  have h := Primrec.option_bind GorbowNumeralPrefixCodeProof.uniformPrograms.2.1 pr_eqInner.to₂
  exact h.of_eq (fun raw => by
    cases hp : GorbowNumeralPrefixCode.parse raw <;> simp [equationArgs,hp]
    case some p => cases GorbowNumeralPrefixCode.decode p.2 <;> rfl)
private theorem pr_relation (positive : Bool) : Primrec (fun raw : List Nat =>
    ((GorbowNumeralPrefixCode.decode raw).map (fun n => if positive then GorbowSortedRegistry.relationProgram n else !(GorbowSortedRegistry.relationProgram n))).getD false) := by
  have hv : Primrec (fun p : List Nat × Nat => if positive then GorbowSortedRegistry.relationProgram p.2 else !(GorbowSortedRegistry.relationProgram p.2)) :=
    by
      cases positive with
      | false => exact Primrec.not.comp (GorbowSortedRegistryProof.uniformPrograms.1.comp Primrec.snd)
      | true => exact GorbowSortedRegistryProof.uniformPrograms.1.comp Primrec.snd
  exact Primrec.option_getD.comp (Primrec.option_map GorbowNumeralPrefixCodeProof.uniformPrograms.2.2 hv.to₂) (Primrec.const false)
private theorem pr_function : Primrec (fun raw : List Nat =>
    ((equationArgs raw).map (fun p => decide (GorbowAtomicRegistry.functionProgram p.1=p.2))).getD false) := by
  have hv : Primrec (fun p : List Nat × (Nat × Nat) => decide (GorbowAtomicRegistry.functionProgram p.2.1=p.2.2)) :=
    (Primrec.eq.comp (GorbowAtomicRegistryProof.uniformPrograms.2.comp (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd)).decide
  exact Primrec.option_getD.comp (Primrec.option_map pr_equationArgs hv.to₂) (Primrec.const false)
private theorem pr_axiom : Primrec axiomProgram := by
  have hd (n : Nat) : Primrec (fun raw : List Nat => raw.drop n) := Primrec.list_drop.comp (Primrec.const n) Primrec.id
  have ht (n : Nat) (pref : List Nat) : PrimrecPred (fun raw : List Nat => raw.take n=pref) :=
    Primrec.eq.comp (Primrec.list_take.comp (Primrec.const n) Primrec.id) (Primrec.const pref)
  have h := Primrec.ite (ht 1 [1]) ((pr_relation true).comp (hd 1))
    (Primrec.ite (ht 2 [6,1]) ((pr_relation false).comp (hd 2))
      (Primrec.ite (ht 2 [0,5]) (pr_function.comp (hd 2)) (Primrec.const false)))
  exact h.of_eq (fun raw => by simp [axiomProgram])

theorem uniformPrograms : Comparators.GorbowRegistryDiagram.UniformPrograms := ⟨pr_equationArgs,pr_axiom⟩
theorem gorbowRegistryDiagram : Comparators.GorbowRegistryDiagram.Target :=
  ⟨equationArgsExact,exactProgram,actualTheory,diagramSoundness,theorySoundness,numeralwiseRepresentation,diagramConsistency,uniformPrograms⟩
end LogicLineages.ComputabilityKnowledge.GorbowRegistryDiagramProof
