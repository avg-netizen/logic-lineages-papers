module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowNumeralPrefixCode
public import LogicLineages.ComputabilityKnowledge.GorbowCodeConstructorsProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowNumeralPrefixCodeProof
open GorbowSyntax GorbowNumeralPrefixCode GorbowCodeConstructors

private theorem parseSucc (raw : List Nat) :
    parse (2::raw)=(parse raw).map (fun p => (p.1+1,p.2)) := by
  have hc : leadingSucc (2::raw)=leadingSucc raw+1 := by simp [leadingSucc]
  unfold parse
  rw [hc]
  change (if raw[leadingSucc raw]?=some 1 then some (leadingSucc raw+1,raw.drop (leadingSucc raw+1)) else none)=_
  split <;> simp_all

private theorem prefixSound (raw : List Nat) : ∀ n rest,
    parse raw=some (n,rest) → raw=numeral n ++ rest := by
  induction raw with
  | nil => intro n rest h; simp [parse,leadingSucc] at h
  | cons tag tail ih =>
    intro n rest h
    by_cases h2 : tag=2
    · subst tag
      rw [parseSucc] at h
      cases hp : parse tail with
      | none => simp [hp] at h
      | some p =>
        rcases p with ⟨j,suffix⟩
        have he : (j+1,suffix)=(n,rest) := Option.some.inj (by simpa [hp] using h)
        have hj : j+1=n := congrArg Prod.fst he
        have hr : suffix=rest := congrArg Prod.snd he
        subst n
        subst rest
        simp only [numeral,List.replicate_succ,List.cons_append]
        exact congrArg (List.cons 2) (ih j suffix hp)
    · by_cases h1 : tag=1
      · subst tag
        have he : (0,tail)=(n,rest) := Option.some.inj (by simpa [parse,leadingSucc] using h)
        cases he
        rfl
      · simp [parse,leadingSucc,h2,h1] at h

private theorem prefixComplete (n : Nat) (rest : List Nat) : parse (numeral n ++ rest)=some (n,rest) := by
  induction n with
  | zero => simp [parse,leadingSucc,numeral]
  | succ n ih =>
    simpa only [numeral,List.replicate_succ,List.cons_append,parseSucc,ih,Option.map_some] using
      congrArg (Option.map (fun p : Nat × List Nat => (p.1+1,p.2))) ih

theorem prefixExact : Comparators.GorbowNumeralPrefixCode.PrefixExact := by
  intro raw n rest
  exact ⟨prefixSound raw n rest,fun h => h ▸ prefixComplete n rest⟩

theorem closedExact : Comparators.GorbowNumeralPrefixCode.ClosedExact := by
  intro raw n
  constructor
  · intro h
    cases hp : parse raw with
    | none => simp [decode,hp] at h
    | some p =>
      rcases p with ⟨j,rest⟩
      by_cases hr : rest=[]
      · subst rest
        have hj : j=n := by simpa [decode,hp] using h
        subst n
        simpa using (prefixExact raw j []).mp hp
      · simp [decode,hp,hr] at h
  · intro h
    subst raw
    have hp : parse (numeral n)=some (n,[]) := by simpa using prefixComplete n []
    simp [decode,hp]

theorem typedCalibration : Comparators.GorbowNumeralPrefixCode.TypedCalibration := by
  intro k n rest
  have he := GorbowCodeConstructorsProof.numeralCalibration k n
  rw [he]
  exact ⟨prefixComplete n rest,(closedExact _ n).mpr rfl⟩

theorem rejection : Comparators.GorbowNumeralPrefixCode.Rejection := by
  constructor
  · intro raw
    constructor
    · intro h ⟨n,rest,he⟩
      have hp := (prefixExact raw n rest).mpr he
      simp [h] at hp
    · intro h
      cases hp : parse raw with
      | none => rfl
      | some p => exact False.elim (h ⟨p.1,p.2,(prefixExact raw p.1 p.2).mp hp⟩)
  · intro raw
    constructor
    · intro h ⟨n,he⟩
      have hp := (closedExact raw n).mpr he
      simp [h] at hp
    · intro h
      cases hp : decode raw with
      | none => rfl
      | some n => exact False.elim (h ⟨n,(closedExact raw n).mp hp⟩)

private theorem pr_leading : Primrec leadingSucc := by
  have hs : Primrec (fun p : List Nat × Nat × Nat => if p.2.1=2 then p.2.2+1 else 0) :=
    Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 2))
      (Primrec.succ.comp (Primrec.snd.comp Primrec.snd)) (Primrec.const 0)
  exact Primrec.list_foldr Primrec.id (Primrec.const 0) hs.to₂

private theorem pr_parse : Primrec parse := by
  have hi : Primrec (fun raw : List Nat => raw[leadingSucc raw]?) := Primrec.list_getElem?.comp Primrec.id pr_leading
  have hd : Primrec (fun raw : List Nat => raw.drop (leadingSucc raw+1)) :=
    Primrec.list_drop.comp (Primrec.succ.comp pr_leading) Primrec.id
  exact Primrec.ite (Primrec.eq.comp hi (Primrec.const (some 1)))
    (Primrec.option_some.comp (pr_leading.pair hd)) (Primrec.const none)

private theorem pr_decode : Primrec decode := by
  have hs : Primrec (fun p : List Nat × (Nat × List Nat) =>
      if p.2.2=[] then some p.2.1 else none) :=
    Primrec.ite (Primrec.eq.comp (Primrec.snd.comp Primrec.snd) (Primrec.const []))
      (Primrec.option_some.comp (Primrec.fst.comp Primrec.snd)) (Primrec.const none)
  have h := Primrec.option_casesOn pr_parse (Primrec.const none) hs.to₂
  exact h.of_eq (fun raw => by cases hp : parse raw <;> simp [decode,hp])

theorem uniformPrograms : Comparators.GorbowNumeralPrefixCode.UniformPrograms := ⟨pr_leading,pr_parse,pr_decode⟩

theorem gorbowNumeralPrefixCode : Comparators.GorbowNumeralPrefixCode.Target :=
  ⟨prefixExact,closedExact,typedCalibration,rejection,uniformPrograms⟩
end LogicLineages.ComputabilityKnowledge.GorbowNumeralPrefixCodeProof
