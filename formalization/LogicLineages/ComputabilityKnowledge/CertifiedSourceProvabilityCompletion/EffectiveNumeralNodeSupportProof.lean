module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.EffectiveNumeralTransportProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRChildTagsProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRSubtreeProof

@[expose] public section
/-! A finite auxiliary checker listing only the fixed program's actual node
equations at a runtime tag. Every axiom is transported to the original ambient
registry by actual subtree lookup; source S/D is never extended. -/
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.EffectiveNumeral.NodeSupport
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowPRChildTags

/-- Recursively listed exact node equations, with the original child offsets. -/
def supportAxioms : {n : Nat} → Program n → Nat → List Sentence
  | _, .zero, tag => nodeEquations .zero tag
  | _, .succ, tag => nodeEquations .succ tag
  | _, .projection i, tag => nodeEquations (.projection i) tag
  | _, .composition f g, tag =>
      nodeEquations (.composition f g) tag ++
        (supportAxioms f (tag+1) ++
          (List.ofFn fun i => supportAxioms (g i) (tag+argumentTag f g i)).flatten)
  | _, .recursion f g, tag =>
      nodeEquations (.recursion f g) tag ++
        (supportAxioms f (tag+1) ++ supportAxioms g (tag+stepTag f))

def check {n : Nat} (q : Program n) (tag : Nat) (raw : List Nat) : Bool :=
  decide (raw ∈ (supportAxioms q tag).map GorbowFormulaPrefixCode.encode)

theorem rootIncluded {n : Nat} (q : Program n) tag sigma
    (h : sigma ∈ nodeEquations q tag) : sigma ∈ supportAxioms q tag := by
  cases q with
  | zero => exact h
  | succ => exact h
  | projection i => exact h
  | composition f g => exact List.mem_append_left _ h
  | recursion f g => exact List.mem_append_left _ h

theorem functionIncluded {m k : Nat} (f : Program k) (g : Fin k → Program m) tag sigma
    (h : sigma ∈ supportAxioms f (tag+1)) : sigma ∈ supportAxioms (.composition f g) tag :=
  List.mem_append_right _ (List.mem_append_left _ h)

theorem argumentIncluded {m k : Nat} (f : Program k) (g : Fin k → Program m) tag i sigma
    (h : sigma ∈ supportAxioms (g i) (tag+argumentTag f g i)) :
    sigma ∈ supportAxioms (.composition f g) tag :=
  List.mem_append_right _ (List.mem_append_right _ (List.mem_flatten.mpr
    ⟨_, List.mem_ofFn.mpr ⟨i, rfl⟩, h⟩))

theorem baseIncluded {m : Nat} (f : Program m) (g : Program (m+2)) tag sigma
    (h : sigma ∈ supportAxioms f (tag+1)) : sigma ∈ supportAxioms (.recursion f g) tag :=
  List.mem_append_right _ (List.mem_append_left _ h)

theorem stepIncluded {m : Nat} (f : Program m) (g : Program (m+2)) tag sigma
    (h : sigma ∈ supportAxioms g (tag+stepTag f)) : sigma ∈ supportAxioms (.recursion f g) tag :=
  List.mem_append_right _ (List.mem_append_right _ h)

private theorem nodeMember {n m : Nat} (p : Program n) (tag : Nat) (q : Program m)
    (ht : (nodes p)[tag]? = some ⟨m,q⟩) (sigma : Sentence)
    (hs : sigma ∈ nodeEquations q tag) : sigma ∈ axioms p := by
  have hb : tag < (nodes p).length := by
    by_contra hn
    have he := List.getElem?_eq_none (l := nodes p) (Nat.le_of_not_gt hn)
    rw [ht] at he
    cases he
  have helem : (nodes p)[tag] = ⟨m,q⟩ := by simpa [hb] using ht
  apply List.mem_flatMap.mpr
  refine ⟨(⟨m,q⟩,tag), ?_, hs⟩
  apply List.mem_iff_getElem.mpr
  refine ⟨tag, by simpa using hb, ?_⟩
  simp [helem]

private theorem childLookup {n m : Nat} (p : Program n) (tag : Nat) (q : Program m)
    (ht : (nodes p)[tag]? = some ⟨m,q⟩) (offset : Nat) (a : Packed)
    (hl : (nodes q)[offset]? = some a) : (nodes p)[tag+offset]? = some a :=
  GorbowPRSubtree.Proof.lookupTransport n p tag ⟨m,q⟩ offset a ht hl

/-- No semantic truth-to-proof argument: literal finite source membership. -/
theorem intoRegistry {m : Nat} (q : Program m) :
    ∀ n (p : Program n) tag, (nodes p)[tag]? = some ⟨m,q⟩ →
      ∀ sigma ∈ supportAxioms q tag, sigma ∈ axioms p := by
  induction q with
  | zero => intro n p tag ht sigma hs; exact nodeMember p tag .zero ht sigma hs
  | succ => intro n p tag ht sigma hs; exact nodeMember p tag .succ ht sigma hs
  | projection i => intro n p tag ht sigma hs; exact nodeMember p tag (.projection i) ht sigma hs
  | @composition m k f g ihf ihg =>
      intro n p tag ht sigma hs
      rcases List.mem_append.mp hs with hs | hs
      · exact nodeMember p tag (.composition f g) ht sigma hs
      · rcases List.mem_append.mp hs with hs | hs
        · exact ihf n p (tag+1)
            (childLookup p tag (.composition f g) ht 1 ⟨k,f⟩
              (GorbowPRChildTags.Proof.compositionFunction m k f g)) sigma hs
        · obtain ⟨part,hpart,hs⟩ := List.mem_flatten.mp hs
          obtain ⟨i,hi⟩ := List.mem_ofFn.mp hpart
          subst part
          exact ihg i n p (tag+argumentTag f g i)
            (childLookup p tag (.composition f g) ht _ _
              (GorbowPRChildTags.Proof.compositionArgument m k f g i)) sigma hs
  | @recursion m f g ihf ihg =>
      intro n p tag ht sigma hs
      rcases List.mem_append.mp hs with hs | hs
      · exact nodeMember p tag (.recursion f g) ht sigma hs
      · rcases List.mem_append.mp hs with hs | hs
        · exact ihf n p (tag+1)
            (childLookup p tag (.recursion f g) ht 1 ⟨m,f⟩
              (GorbowPRChildTags.Proof.recursionBase m f g)) sigma hs
        · exact ihg n p (tag+stepTag f)
            (childLookup p tag (.recursion f g) ht _ _
              (GorbowPRChildTags.Proof.recursionStep m f g)) sigma hs

theorem checkIntoRegistry {m n : Nat} (q : Program m) (p : Program n) tag
    (ht : (nodes p)[tag]? = some ⟨m,q⟩) (raw : List Nat) (h : check q tag raw = true) :
    registryAxiomCheck p raw = true := by
  simp only [check, registryAxiomCheck, decide_eq_true_eq] at h ⊢
  obtain ⟨sigma,hsigma,he⟩ := List.mem_map.mp h
  exact List.mem_map.mpr ⟨sigma, intoRegistry q n p tag ht sigma hsigma, he⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.EffectiveNumeral.NodeSupport
