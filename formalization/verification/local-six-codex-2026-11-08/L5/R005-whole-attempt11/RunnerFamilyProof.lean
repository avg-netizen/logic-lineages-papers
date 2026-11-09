module
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.RunnerTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.RunnerProof
open PolynomialGraphCompletion WordLinearDecisionCompletion Runner
open LogicLineages.ModelsAlgebra.Forests

private theorem tokens_conj (p q : Formula) :
    Formula.tokens (.conj p q) = Formula.tokens p++Formula.tokens q := by
  simp [Formula.tokens,CotreePresburgerUnit.Boolean.atoms,List.flatMap_append]

private theorem allowed_conj (D : Nat) (p q : Formula)
    (hp : Formula.allowed D p) (hq : Formula.allowed D q) : Formula.allowed D (.conj p q) := by
  intro t ht
  rw [tokens_conj] at ht
  rcases List.mem_append.mp ht with ht | ht
  · exact hp t ht
  · exact hq t ht

private theorem meaningful_conj (p q : Formula) (ν : Nat → Nat)
    (hp : Formula.meaningful p ν) (hq : Formula.meaningful q ν) : Formula.meaningful (.conj p q) ν := by
  intro t ht
  rw [tokens_conj] at ht
  rcases List.mem_append.mp ht with ht | ht
  · exact hp t ht
  · exact hq t ht

private theorem linear_conj (maximum : Nat) (p q : Formula)
    (hp : linear maximum p = true) (hq : linear maximum q = true) : linear maximum (.conj p q) = true := by
  simp only [linear,tokens_conj,List.all_append,Bool.and_eq_true]
  exact ⟨hp,hq⟩

private theorem append_forall₂ {α β : Type} {R : α → β → Prop}
    {leftRows : List α} {leftOut : List β} {rightRows : List α} {rightOut : List β}
    (hl : List.Forall₂ R leftRows leftOut) (hr : List.Forall₂ R rightRows rightOut) :
    List.Forall₂ R (leftRows++rightRows) (leftOut++rightOut) := by
  induction hl with
  | nil => exact hr
  | cons hhead htail ih => exact List.Forall₂.cons hhead ih

/-- Actual Cartesian case product, with original names and source row order.
Both guards are interpreted at the same original valuation. -/
theorem combinePackage_correct (D maximum : Nat) (leftRows rightRows : List Row)
    (left right : Package) (hleft : PackageCorrect D maximum leftRows left)
    (hright : PackageCorrect D maximum rightRows right) :
    PackageCorrect D maximum (leftRows++rightRows) (combinePackage left right) := by
  have hnleft : ∀ i ∈ OriginalNames leftRows, i ∈ OriginalNames (leftRows++rightRows) := by
    intro i hi
    simpa only [OriginalNames,List.flatMap_append] using List.mem_append_left (OriginalNames rightRows) hi
  have hnright : ∀ i ∈ OriginalNames rightRows, i ∈ OriginalNames (leftRows++rightRows) := by
    intro i hi
    simpa only [OriginalNames,List.flatMap_append] using List.mem_append_right (OriginalNames leftRows) hi
  constructor
  · intro c hc
    obtain ⟨l,hl,hc⟩ := List.mem_flatMap.mp hc
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hc
    rcases hleft.1 l hl with ⟨haL,hlL,hnL,hcountL,houtL⟩
    rcases hright.1 r hr with ⟨haR,hlR,hnR,hcountR,houtR⟩
    refine ⟨allowed_conj D _ _ haL haR,linear_conj maximum _ _ hlL hlR,?_,?_,?_⟩
    · intro i hi
      have hm : i ∈ Formula.variables l.guard ∨ i ∈ Formula.variables r.guard := by
        simpa [combineCase,Formula.variables,tokens_conj,List.map_append] using hi
      rcases hm with hi | hi
      · exact hnleft i (hnL i hi)
      · exact hnright i (hnR i hi)
    · simp [combineCase,List.length_append,hcountL,hcountR]
    · intro o ho
      rcases List.mem_append.mp ho with ho | ho
      · have h := houtL o ho
        exact ⟨h.1,fun i hi => hnleft i (h.2.1 i hi),h.2.2⟩
      · have h := houtR o ho
        exact ⟨h.1,fun i hi => hnright i (h.2.1 i hi),h.2.2⟩
  · intro ν hregion
    have hRL : Region left.tail maximum (OriginalNames leftRows) ν := by
      intro i hi
      have h := hregion i (hnleft i hi)
      exact ⟨(Nat.le_max_left _ _).trans h.1,h.2⟩
    have hRR : Region right.tail maximum (OriginalNames rightRows) ν := by
      intro i hi
      have h := hregion i (hnright i hi)
      exact ⟨(Nat.le_max_right _ _).trans h.1,h.2⟩
    rcases hleft.2 ν hRL with ⟨hdomL,hcasesL,hcoverL,hcorrectL⟩
    rcases hright.2 ν hRR with ⟨hdomR,hcasesR,hcoverR,hcorrectR⟩
    refine ⟨?_,?_,?_,?_⟩
    · intro row hrow
      rcases List.mem_append.mp hrow with hrow | hrow
      · exact hdomL row hrow
      · exact hdomR row hrow
    · intro c hc
      obtain ⟨l,hl,hc⟩ := List.mem_flatMap.mp hc
      obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hc
      refine ⟨meaningful_conj _ _ ν (hcasesL l hl).1 (hcasesR r hr).1,?_⟩
      intro o ho
      rcases List.mem_append.mp ho with ho | ho
      · exact (hcasesL l hl).2 o ho
      · exact (hcasesR r hr).2 o ho
    · obtain ⟨l,hl,hltrue⟩ := hcoverL
      obtain ⟨r,hr,hrtrue⟩ := hcoverR
      exact ⟨combineCase l r,List.mem_flatMap.mpr ⟨l,hl,List.mem_map.mpr ⟨r,hr,rfl⟩⟩,
        And.intro hltrue hrtrue⟩
    · intro c hc htrue
      obtain ⟨l,hl,hc⟩ := List.mem_flatMap.mp hc
      obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hc
      exact append_forall₂ (hcorrectL l hl htrue.1) (hcorrectR r hr htrue.2)

theorem emptyFamily_correct (D maximum : Nat) : PackageCorrect D maximum [] emptyFamily := by
  constructor
  · intro c hc
    have he : c = ⟨.top,[]⟩ := by simpa [emptyFamily] using hc
    subst c
    simp [Formula.allowed,linear,FormulaNamesFrom,Formula.variables,Formula.tokens,
      CotreePresburgerUnit.Boolean.atoms]
  · intro ν hregion
    refine ⟨by simp,?_,?_,?_⟩
    · intro c hc
      have he : c = ⟨.top,[]⟩ := by simpa [emptyFamily] using hc
      subst c
      simp [Formula.meaningful,Formula.tokens,CotreePresburgerUnit.Boolean.atoms]
    · exact ⟨⟨.top,[]⟩,by simp [emptyFamily],True.intro⟩
    · intro c hc htrue
      have he : c = ⟨.top,[]⟩ := by simpa [emptyFamily] using hc
      subst c
      exact List.Forall₂.nil

theorem familyPackage_of_single (hsingle : RunnerTargets.ExactSingleRowPackage) :
    RunnerTargets.ExactFamilyPackage := by
  intro D maximum rows hDegree hrows
  induction rows with
  | nil => exact emptyFamily_correct D maximum
  | cons r rows ih =>
      have hrow := hsingle D maximum r hDegree (hrows r (by simp))
      have hrest := ih (fun s hs => hrows s (by simp [hs]))
      exact combinePackage_correct D maximum [r] rows (solve D maximum r)
        (compile D maximum rows) hrow hrest

end LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.RunnerProof
