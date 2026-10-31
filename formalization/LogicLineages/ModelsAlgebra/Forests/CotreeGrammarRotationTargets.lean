module
public import LogicLineages.ModelsAlgebra.Forests.CotreeGrammarRotationDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreeGrammarRotation.Targets
open CotreeGrammarOpen CotreeGrammarFlow

def ComposePlug : Prop := ∀ (Q : Type) (δ : Q → Q → Q) r q s
  (C : Context δ r q) (D : Context δ q s) (t : Tree δ s),
  plug (compose C D) t = plug C (plug D t)

def ComposeCounts : Prop := ∀ (Q : Type) [DecidableEq Q] (δ : Q → Q → Q) r q s
  (C : Context δ r q) (D : Context δ q s),
  contextCounts (compose C D) = addCounts (contextCounts C) (contextCounts D)

def ContextHolesLaw : Prop := ∀ (Q : Type) [DecidableEq Q] (δ : Q → Q → Q) r q
  (C : Context δ r q) (t : Tree δ q) x,
  (holes (plug C t)).count x = (contextHoles C).count x + (holes t).count x

def FillCounts : Prop := ∀ (Q : Type) [DecidableEq Q] (δ : Q → Q → Q) r x y
  (C : TwoContext δ r x y) (u : Tree δ x) (v : Tree δ y),
  counts (fill C u v) = addCounts (addCounts (twoCounts C) (counts u)) (counts v)

def TwoHolesLaw : Prop := ∀ (Q : Type) [DecidableEq Q] (δ : Q → Q → Q) r x y
  (C : TwoContext δ r x y) (u : Tree δ x) (v : Tree δ y) z,
  (holes (fill C u v)).count z = (twoHoles C).count z + (holes u).count z + (holes v).count z

/-- Rotation at a node on the distinguished root-to-hole path. -/
def OnPathRotation : Prop := ∀ (Q : Type) [DecidableEq Q] (δ : Q → Q → Q) x y
  (C : Context δ x y) (D : Context δ y x),
  counts (plug (compose C D) (.hole x)) = counts (plug (compose D C) (.hole y)) ∧
  (holes (plug (compose C D) (.hole x)) = [x] →
    holes (plug (compose D C) (.hole y)) = [y])

/-- The distinct off-spine case, with both the cut occurrence and original
cycle hole tracked explicitly. No ill-typed one-hole rotation is substituted. -/
def OffPathRotation : Prop := ∀ (Q : Type) [DecidableEq Q] (δ : Q → Q → Q) x y
  (C : TwoContext δ x y x) (D : Context δ y x) (t : Tree δ x),
  counts (fill C (plug D t) (.hole x)) = counts (plug D (fill C (.hole y) t)) ∧
  (holes (fill C (plug D t) (.hole x)) = [x] →
    holes (plug D (fill C (.hole y) t)) = [y])

def OccurrenceFactorization : Prop := ∀ (Q : Type) (δ : Q → Q → Q) r (t : Tree δ r) x,
  Occurs x t ↔ ∃ (C : Context δ r x) (u : Tree δ x), plug C u = t

/-- Every node occurrence is on the distinguished path or in an actual sibling,
with concrete one- or two-hole factorizations, respectively. -/
def ContextDichotomy : Prop := ∀ (Q : Type) (δ : Q → Q → Q) r x
  (C : Context δ r x) y, Occurs y (plug C (.hole x)) →
  (∃ (P : Context δ r y) (S : Context δ y x), C = compose P S) ∨
  ∃ (D : TwoContext δ r y x) (t : Tree δ y), ∀ u : Tree δ x, plug C u = fill D t u

end LogicLineages.ModelsAlgebra.Forests.CotreeGrammarRotation.Targets
