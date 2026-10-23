import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.Fintype.Pi

/-!
# Finite pure-pattern syntax and maps

Vertices have the fixed linear order `Fin n`. Each Boolean table stores
the **strict** part of a higher relation; reflexivity is implicit. For
`k = 1` these are the finite pure-R1 syntactic inputs of the calculator.
Larger `k` describes finite nested-relation syntax only.

These definitions do not define resemblance by elementarity inside a
finite structure. Identifying arithmetic traces with the inherited global
semantic R1 relation is a separate published mathematical input.
-/

namespace R1Calculator

variable {n m l p k : Nat}

/-- Raw finite relation tables and an optional designated vertex. -/
structure PatternData (n k : Nat) where
  edge : Fin k → Fin n → Fin n → Bool
  marker : Option (Fin n) := none

namespace PatternData

/-- Read a level by its natural index; an absent level has no strict edges. -/
def edgeAt (P : PatternData n k) (r : Nat) (x y : Fin n) : Bool :=
  if h : r < k then P.edge ⟨r, h⟩ x y else false

/-- The preceding strict relation: the linear order before level zero. -/
def previous (P : PatternData n k) (r : Fin k) (x y : Fin n) : Bool :=
  if r.val = 0 then decide (x < y) else P.edgeAt (r.val - 1) x y

/-- The actual nesting/transitivity/respect laws on strict finite tables. -/
def Valid (P : PatternData n k) : Prop :=
  0 < k ∧
  (∀ r x y, P.edge r x y = true → x < y) ∧
  (∀ r x y, P.edge r x y = true → P.previous r x y = true) ∧
  (∀ r x y z, P.edge r x y = true → P.edge r y z = true → P.edge r x z = true) ∧
  (∀ r x y z, x < y → y < z → P.previous r x y = true →
    P.previous r y z = true → P.edge r x z = true → P.edge r x y = true)

private def allFin (n : Nat) (p : Fin n → Bool) : Bool :=
  (List.finRange n).all p

private theorem allFin_eq_true (p : Fin n → Bool) :
    allFin n p = true ↔ ∀ x, p x = true := by
  simp [allFin, List.all_eq_true]

private def impliesB (a b : Bool) : Bool := !a || b

private theorem impliesB_eq_true (a b : Bool) :
    impliesB a b = true ↔ (a = true → b = true) := by
  cases a <;> cases b <;> decide

/-- Check strict upper-triangularity by visiting every stored relation bit. -/
def checkUpper (P : PatternData n k) : Bool :=
  allFin k fun r => allFin n fun x => allFin n fun y =>
    impliesB (P.edge r x y) (decide (x < y))

/-- Check inclusion in the preceding strict relation. -/
def checkNested (P : PatternData n k) : Bool :=
  allFin k fun r => allFin n fun x => allFin n fun y =>
    impliesB (P.edge r x y) (P.previous r x y)

/-- Check transitivity over all triples of vertices. -/
def checkTransitive (P : PatternData n k) : Bool :=
  allFin k fun r => allFin n fun x => allFin n fun y => allFin n fun z =>
    impliesB (P.edge r x y && P.edge r y z) (P.edge r x z)

/-- Check respect for the preceding relation, with the original order guards. -/
def checkRespect (P : PatternData n k) : Bool :=
  allFin k fun r => allFin n fun x => allFin n fun y => allFin n fun z =>
    impliesB (decide (x < y) && decide (y < z) &&
      P.previous r x y && P.previous r y z && P.edge r x z) (P.edge r x y)

/-- Executable validation, including the nonempty relation signature. -/
def check (P : PatternData n k) : Bool :=
  decide (0 < k) && P.checkUpper && P.checkNested && P.checkTransitive && P.checkRespect

theorem checkUpper_eq_true (P : PatternData n k) :
    P.checkUpper = true ↔ ∀ r x y, P.edge r x y = true → x < y := by
  simp [checkUpper, allFin_eq_true, impliesB_eq_true]

theorem checkNested_eq_true (P : PatternData n k) :
    P.checkNested = true ↔ ∀ r x y, P.edge r x y = true → P.previous r x y = true := by
  simp [checkNested, allFin_eq_true, impliesB_eq_true]

theorem checkTransitive_eq_true (P : PatternData n k) :
    P.checkTransitive = true ↔
      ∀ r x y z, P.edge r x y = true → P.edge r y z = true → P.edge r x z = true := by
  simp [checkTransitive, allFin_eq_true, impliesB_eq_true, Bool.and_eq_true, and_imp]

theorem checkRespect_eq_true (P : PatternData n k) :
    P.checkRespect = true ↔
      ∀ r x y z, x < y → y < z → P.previous r x y = true →
        P.previous r y z = true → P.edge r x z = true → P.edge r x y = true := by
  simp [checkRespect, allFin_eq_true, impliesB_eq_true, Bool.and_eq_true, and_imp]

/-- The finite Boolean checker accepts exactly the stated pattern laws. -/
theorem check_eq_true_iff_valid (P : PatternData n k) :
    P.check = true ↔ P.Valid := by
  simp [check, Valid, Bool.and_eq_true, checkUpper_eq_true, checkNested_eq_true,
    checkTransitive_eq_true, checkRespect_eq_true, and_assoc]

instance (P : PatternData n k) : Decidable P.Valid :=
  decidable_of_iff (P.check = true) P.check_eq_true_iff_valid

/-- Reflexive closure of a stored strict relation, not finite elementarity. -/
def Weak (P : PatternData n k) (r : Fin k) (x y : Fin n) : Prop :=
  x = y ∨ P.edge r x y = true

theorem Valid.upper {P : PatternData n k} (h : P.Valid) (r : Fin k) (x y : Fin n)
    (hxy : P.edge r x y = true) : x < y := h.2.1 r x y hxy

theorem Valid.nested {P : PatternData n k} (h : P.Valid) (r : Fin k) (x y : Fin n)
    (hxy : P.edge r x y = true) : P.previous r x y = true := h.2.2.1 r x y hxy

theorem weak_refl (P : PatternData n k) (r : Fin k) (x : Fin n) : P.Weak r x x :=
  Or.inl rfl

theorem Valid.weak_transitive {P : PatternData n k} (h : P.Valid) (r : Fin k) :
    ∀ ⦃x y z⦄, P.Weak r x y → P.Weak r y z → P.Weak r x z := by
  intro x y z hxy hyz
  rcases hxy with hxy | hxy
  · subst y; exact hyz
  rcases hyz with hyz | hyz
  · subst z; exact Or.inr hxy
  exact Or.inr (h.2.2.2.1 r x y z hxy hyz)

theorem Valid.weak_antisymm {P : PatternData n k} (h : P.Valid) (r : Fin k)
    {x y : Fin n} (hxy : P.Weak r x y) (hyx : P.Weak r y x) : x = y := by
  rcases hxy with hxy | hxy
  · exact hxy
  rcases hyx with hyx | hyx
  · exact hyx.symm
  exact False.elim (lt_asymm (h.upper r x y hxy) (h.upper r y x hyx))

theorem Valid.weak_le {P : PatternData n k} (h : P.Valid) (r : Fin k)
    {x y : Fin n} (hxy : P.Weak r x y) : x ≤ y := by
  rcases hxy with hxy | hxy
  · exact le_of_eq hxy
  · exact le_of_lt (h.upper r x y hxy)

/-- A proposed map is a strictly increasing injection preserving positive atoms. -/
def IsCovering (P : PatternData n k) (Q : PatternData m k) (f : Fin n → Fin m) : Prop :=
  StrictMono f ∧ ∀ r x y, P.edge r x y = true → Q.edge r (f x) (f y) = true

/-- This checks an explicitly supplied map, not existence by an oracle. -/
def checkCovering (P : PatternData n k) (Q : PatternData m k) (f : Fin n → Fin m) : Bool :=
  (allFin n fun x => allFin n fun y => impliesB (decide (x < y)) (decide (f x < f y))) &&
  (allFin k fun r => allFin n fun x => allFin n fun y =>
    impliesB (P.edge r x y) (Q.edge r (f x) (f y)))

theorem checkCovering_eq_true (P : PatternData n k) (Q : PatternData m k)
    (f : Fin n → Fin m) : P.checkCovering Q f = true ↔ P.IsCovering Q f := by
  simp [checkCovering, IsCovering, StrictMono, allFin_eq_true, impliesB_eq_true]

/-- Induced maps reflect missing atoms as well as preserving positive atoms. -/
def IsInduced (P : PatternData n k) (Q : PatternData m k) (f : Fin n → Fin m) : Prop :=
  P.IsCovering Q f ∧ ∀ r x y, P.edge r x y = Q.edge r (f x) (f y)

def checkInduced (P : PatternData n k) (Q : PatternData m k) (f : Fin n → Fin m) : Bool :=
  P.checkCovering Q f &&
  allFin k fun r => allFin n fun x => allFin n fun y =>
    decide (P.edge r x y = Q.edge r (f x) (f y))

theorem checkInduced_eq_true (P : PatternData n k) (Q : PatternData m k)
    (f : Fin n → Fin m) : P.checkInduced Q f = true ↔ P.IsInduced Q f := by
  simp [checkInduced, IsInduced, checkCovering_eq_true, allFin_eq_true]

end PatternData

/-- Validated syntax. Its marker, if present, is necessarily an actual vertex. -/
structure Pattern (n k : Nat) extends PatternData n k where
  valid : toPatternData.Valid

/-- Checked construction from raw input. Invalid tables return `none`. -/
def validatePattern (P : PatternData n k) : Option (Pattern n k) :=
  if h : P.check = true then some ⟨P, P.check_eq_true_iff_valid.mp h⟩ else none

theorem validatePattern_isSome (P : PatternData n k) :
    (validatePattern P).isSome = P.check := by
  unfold validatePattern
  split <;> simp_all

theorem validatePattern_isSome_iff_valid (P : PatternData n k) :
    (validatePattern P).isSome = true ↔ P.Valid := by
  rw [validatePattern_isSome, PatternData.check_eq_true_iff_valid]

/-- A positive-atom covering; markers impose no condition by default. -/
structure Covering (P : Pattern n k) (Q : Pattern m k) where
  toFun : Fin n → Fin m
  strictMono : StrictMono toFun
  preserve : ∀ r x y, P.edge r x y = true → Q.edge r (toFun x) (toFun y) = true

namespace Covering

variable {P : Pattern n k} {Q : Pattern m k} {R : Pattern l k}

instance : CoeFun (Covering P Q) (fun _ => Fin n → Fin m) := ⟨toFun⟩

theorem injective (f : Covering P Q) : Function.Injective f.toFun := f.strictMono.injective

@[ext] theorem ext {f g : Covering P Q} (h : ∀ x, f x = g x) : f = g := by
  cases f with
  | mk ff hf hp =>
    cases g with
    | mk gg hg hq =>
      have he : ff = gg := funext h
      subst gg
      rfl

def id (P : Pattern n k) : Covering P P where
  toFun := fun x => x
  strictMono := fun _ _ h => h
  preserve := fun _ _ _ h => h

def comp (g : Covering Q R) (f : Covering P Q) : Covering P R where
  toFun := fun x => g (f x)
  strictMono := fun _ _ h => g.strictMono (f.strictMono h)
  preserve := fun r x y h => g.preserve r (f x) (f y) (f.preserve r x y h)

@[simp] theorem id_apply (P : Pattern n k) (x : Fin n) : Covering.id P x = x := rfl
@[simp] theorem comp_apply (g : Covering Q R) (f : Covering P Q) (x : Fin n) :
    g.comp f x = g (f x) := rfl

@[simp] theorem id_comp (f : Covering P Q) : (Covering.id Q).comp f = f := by
  ext x; rfl

@[simp] theorem comp_id (f : Covering P Q) : f.comp (Covering.id P) = f := by
  ext x; rfl

theorem comp_assoc {S : Pattern p k} (h : Covering R S) (g : Covering Q R)
    (f : Covering P Q) : h.comp (g.comp f) = (h.comp g).comp f := by
  ext x; rfl

theorem preserves_weak (f : Covering P Q) (r : Fin k) {x y : Fin n}
    (h : P.toPatternData.Weak r x y) : Q.toPatternData.Weak r (f x) (f y) := by
  rcases h with h | h
  · exact Or.inl (congrArg f.toFun h)
  · exact Or.inr (f.preserve r x y h)

def ofCheck (P : Pattern n k) (Q : Pattern m k) (f : Fin n → Fin m)
    (h : P.toPatternData.checkCovering Q.toPatternData f = true) : Covering P Q where
  toFun := f
  strictMono := ((PatternData.checkCovering_eq_true _ _ _).mp h).1
  preserve := ((PatternData.checkCovering_eq_true _ _ _).mp h).2

end Covering

/-- A covering which is an isomorphism onto its induced finite image. -/
structure InducedEmbedding (P : Pattern n k) (Q : Pattern m k) extends Covering P Q where
  edge_eq : ∀ r x y, P.edge r x y = Q.edge r (toFun x) (toFun y)

namespace InducedEmbedding

variable {P : Pattern n k} {Q : Pattern m k} {R : Pattern l k}

instance : CoeFun (InducedEmbedding P Q) (fun _ => Fin n → Fin m) := ⟨fun f => f.toCovering.toFun⟩

@[ext] theorem ext {f g : InducedEmbedding P Q} (h : ∀ x, f x = g x) : f = g := by
  cases f with
  | mk ff hf =>
    cases g with
    | mk gg hg =>
      have he : ff = gg := Covering.ext h
      subst gg
      rfl

def id (P : Pattern n k) : InducedEmbedding P P where
  toCovering := Covering.id P
  edge_eq := fun _ _ _ => rfl

def comp (g : InducedEmbedding Q R) (f : InducedEmbedding P Q) : InducedEmbedding P R where
  toCovering := g.toCovering.comp f.toCovering
  edge_eq := fun r x y => (f.edge_eq r x y).trans (g.edge_eq r (f x) (f y))

@[simp] theorem id_comp (f : InducedEmbedding P Q) : (InducedEmbedding.id Q).comp f = f := by
  ext x; rfl

@[simp] theorem comp_id (f : InducedEmbedding P Q) : f.comp (InducedEmbedding.id P) = f := by
  ext x; rfl

theorem comp_assoc {S : Pattern p k} (h : InducedEmbedding R S) (g : InducedEmbedding Q R)
    (f : InducedEmbedding P Q) : h.comp (g.comp f) = (h.comp g).comp f := by
  ext x; rfl

theorem map_edge_iff (f : InducedEmbedding P Q) (r : Fin k) (x y : Fin n) :
    Q.edge r (f x) (f y) = true ↔ P.edge r x y = true := by rw [← f.edge_eq]

theorem map_nonedge_iff (f : InducedEmbedding P Q) (r : Fin k) (x y : Fin n) :
    Q.edge r (f x) (f y) = false ↔ P.edge r x y = false := by rw [← f.edge_eq]

theorem map_weak_iff (f : InducedEmbedding P Q) (r : Fin k) (x y : Fin n) :
    Q.toPatternData.Weak r (f x) (f y) ↔ P.toPatternData.Weak r x y := by
  constructor
  · rintro (he | he)
    · exact Or.inl (f.toCovering.injective he)
    · exact Or.inr ((f.map_edge_iff r x y).mp he)
  · exact f.toCovering.preserves_weak r

def ofCheck (P : Pattern n k) (Q : Pattern m k) (f : Fin n → Fin m)
    (h : P.toPatternData.checkInduced Q.toPatternData f = true) : InducedEmbedding P Q where
  toCovering := Covering.ofCheck P Q f
    ((PatternData.checkCovering_eq_true _ _ _).mpr
      ((PatternData.checkInduced_eq_true _ _ _).mp h).1)
  edge_eq := ((PatternData.checkInduced_eq_true _ _ _).mp h).2

end InducedEmbedding

/-- Opt-in marker preservation requires BOTH patterns to have a marker. -/
def PreservesMarker (P : Pattern n k) (Q : Pattern m k) (f : Fin n → Fin m) : Prop :=
  ∃ p q, P.marker = some p ∧ Q.marker = some q ∧ f p = q

def checkMarker (P : Pattern n k) (Q : Pattern m k) (f : Fin n → Fin m) : Bool :=
  match P.marker, Q.marker with
  | some p, some q => decide (f p = q)
  | _, _ => false

theorem checkMarker_eq_true (P : Pattern n k) (Q : Pattern m k) (f : Fin n → Fin m) :
    checkMarker P Q f = true ↔ PreservesMarker P Q f := by
  cases hp : P.marker <;> cases hq : Q.marker <;>
    simp [checkMarker, PreservesMarker, hp, hq, eq_comm]

theorem preservesMarker_id_iff (P : Pattern n k) :
    PreservesMarker P P (fun x => x) ↔ ∃ p, P.marker = some p := by
  constructor
  · rintro ⟨p, q, hp, _, _⟩
    exact ⟨p, hp⟩
  · rintro ⟨p, hp⟩
    exact ⟨p, p, hp, hp, rfl⟩

theorem preservesMarker_comp {P : Pattern n k} {Q : Pattern m k} {R : Pattern l k}
    {f : Fin n → Fin m} {g : Fin m → Fin l}
    (hf : PreservesMarker P Q f) (hg : PreservesMarker Q R g) :
    PreservesMarker P R (fun x => g (f x)) := by
  rcases hf with ⟨p, q, hp, hq, hf⟩
  rcases hg with ⟨q', r, hq', hr, hg⟩
  have hqq : q = q' := Option.some.inj (hq.symm.trans hq')
  refine ⟨p, r, hp, hr, ?_⟩
  exact (congrArg g hf).trans ((congrArg g hqq).trans hg)

/-- Pointed coverings add the marker condition explicitly. -/
structure MarkedCovering (P : Pattern n k) (Q : Pattern m k) extends Covering P Q where
  marker_preserved : PreservesMarker P Q toFun

namespace MarkedCovering

variable {P : Pattern n k} {Q : Pattern m k} {R : Pattern l k}

def id (P : Pattern n k) (p : Fin n) (hp : P.marker = some p) : MarkedCovering P P where
  toCovering := Covering.id P
  marker_preserved := ⟨p, p, hp, hp, rfl⟩

def comp (g : MarkedCovering Q R) (f : MarkedCovering P Q) : MarkedCovering P R where
  toCovering := g.toCovering.comp f.toCovering
  marker_preserved := by
    change PreservesMarker P R (fun x => g.toCovering.toFun (f.toCovering.toFun x))
    exact preservesMarker_comp (f := f.toCovering.toFun) (g := g.toCovering.toFun)
      f.marker_preserved g.marker_preserved

end MarkedCovering

/-- Exhaustive finite map search. This enumerates at most `m^n` functions;
the more economical increasing-tuple enumeration is an implementation choice. -/
def coversCheck (P : Pattern n k) (Q : Pattern m k) : Bool :=
  decide (∃ f : Fin n → Fin m, P.toPatternData.checkCovering Q.toPatternData f = true)

theorem coversCheck_eq_true (P : Pattern n k) (Q : Pattern m k) :
    coversCheck P Q = true ↔ Nonempty (Covering P Q) := by
  simp only [coversCheck, decide_eq_true_eq]
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨Covering.ofCheck P Q f hf⟩
  · rintro ⟨f⟩
    exact ⟨f.toFun, (PatternData.checkCovering_eq_true _ _ _).mpr ⟨f.strictMono, f.preserve⟩⟩

def embedsCheck (P : Pattern n k) (Q : Pattern m k) : Bool :=
  decide (∃ f : Fin n → Fin m, P.toPatternData.checkInduced Q.toPatternData f = true)

theorem embedsCheck_eq_true (P : Pattern n k) (Q : Pattern m k) :
    embedsCheck P Q = true ↔ Nonempty (InducedEmbedding P Q) := by
  simp only [embedsCheck, decide_eq_true_eq]
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨InducedEmbedding.ofCheck P Q f hf⟩
  · rintro ⟨f⟩
    exact ⟨f.toFun, (PatternData.checkInduced_eq_true _ _ _).mpr
      ⟨⟨f.strictMono, f.preserve⟩, f.edge_eq⟩⟩

def markedCoversCheck (P : Pattern n k) (Q : Pattern m k) : Bool :=
  decide (∃ f : Fin n → Fin m,
    P.toPatternData.checkCovering Q.toPatternData f = true ∧ checkMarker P Q f = true)

theorem markedCoversCheck_eq_true (P : Pattern n k) (Q : Pattern m k) :
    markedCoversCheck P Q = true ↔ Nonempty (MarkedCovering P Q) := by
  simp only [markedCoversCheck, decide_eq_true_eq]
  constructor
  · rintro ⟨f, hf, hm⟩
    exact ⟨{ toCovering := Covering.ofCheck P Q f hf,
             marker_preserved := (checkMarker_eq_true _ _ _).mp hm }⟩
  · rintro ⟨f⟩
    exact ⟨f.toFun,
      (PatternData.checkCovering_eq_true _ _ _).mpr ⟨f.strictMono, f.preserve⟩,
      (checkMarker_eq_true _ _ _).mpr f.marker_preserved⟩

/-- The relation-free pattern on any finite linear order. -/
def discreteData (n : Nat) : PatternData n 1 where
  edge := fun _ _ _ => false

theorem discreteData_valid (n : Nat) : (discreteData n).Valid := by
  simp [PatternData.Valid, discreteData]

def discrete (n : Nat) : Pattern n 1 := ⟨discreteData n, discreteData_valid n⟩

/-- The pattern whose sole strict higher relation is the strict linear order. -/
def chainData (n : Nat) : PatternData n 1 where
  edge := fun _ x y => decide (x < y)

theorem chainData_valid (n : Nat) : (chainData n).Valid := by
  refine ⟨by decide, ?_, ?_, ?_, ?_⟩
  · intro r x y h
    simpa [chainData] using h
  · intro r x y h
    have hr : r.val = 0 := congrArg Fin.val (Fin.eq_zero r)
    simpa [PatternData.previous, hr, chainData] using h
  · intro r x y z hxy hyz
    have hxy' : x < y := by simpa [chainData] using hxy
    have hyz' : y < z := by simpa [chainData] using hyz
    simpa [chainData] using lt_trans hxy' hyz'
  · intro r x y z hxy _ _ _ _
    simpa [chainData] using hxy

def chain (n : Nat) : Pattern n 1 := ⟨chainData n, chainData_valid n⟩

def discreteToChain (n : Nat) : Covering (discrete n) (chain n) where
  toFun := fun x => x
  strictMono := fun _ _ h => h
  preserve := by intro r x y h; simp [discrete, discreteData] at h

/-- A positive covering need not reflect a missing relation atom. -/
theorem no_induced_discrete_two_chain_two :
    ¬ Nonempty (InducedEmbedding (discrete 2) (chain 2)) := by
  rintro ⟨f⟩
  have hlt : f (0 : Fin 2) < f (1 : Fin 2) := f.strictMono (by decide)
  have he := f.edge_eq (0 : Fin 1) (0 : Fin 2) (1 : Fin 2)
  simp [discrete, chain, discreteData, chainData, hlt] at he

example : (chainData 3).check = true :=
  (PatternData.check_eq_true_iff_valid _).mpr (chainData_valid 3)

example : (discreteData 2).checkCovering (chainData 2) (fun x => x) = true := by decide
example : (discreteData 2).checkInduced (chainData 2) (fun x => x) = false := by decide
example : checkMarker (discrete 2) (discrete 2) (fun x => x) = false := by decide
example : coversCheck (discrete 2) (chain 2) = true := by decide
example : embedsCheck (discrete 2) (chain 2) = false := by decide
example : markedCoversCheck (discrete 2) (discrete 2) = false := by decide

/-- A diagonal strict edge is rejected. -/
def diagonalData : PatternData 1 1 where edge := fun _ _ _ => true
example : diagonalData.check = false := by decide

/-- Transitivity fails even though the two displayed edges are upper triangular. -/
def nontransitiveData : PatternData 3 1 where
  edge := fun _ x y => decide ((x.val = 0 ∧ y.val = 1) ∨ (x.val = 1 ∧ y.val = 2))
example : nontransitiveData.check = false := by decide

/-- The long edge alone fails respect for the intervening linear point. -/
def nonrespectingData : PatternData 3 1 where
  edge := fun _ x y => decide (x.val = 0 ∧ y.val = 2)
example : nonrespectingData.check = false := by decide

/-- A higher relation must be contained in its preceding relation. -/
def nonnestedData : PatternData 2 2 where
  edge := fun r x y => decide (r.val = 1 ∧ x < y)
example : nonnestedData.check = false := by decide

#print axioms PatternData.check_eq_true_iff_valid
#print axioms validatePattern_isSome_iff_valid
#print axioms PatternData.Valid.weak_transitive
#print axioms PatternData.Valid.weak_antisymm
#print axioms PatternData.checkCovering_eq_true
#print axioms PatternData.checkInduced_eq_true
#print axioms Covering.comp
#print axioms Covering.comp_assoc
#print axioms InducedEmbedding.comp
#print axioms InducedEmbedding.map_weak_iff
#print axioms preservesMarker_comp
#print axioms coversCheck_eq_true
#print axioms embedsCheck_eq_true
#print axioms markedCoversCheck_eq_true
#print axioms no_induced_discrete_two_chain_two

end R1Calculator
