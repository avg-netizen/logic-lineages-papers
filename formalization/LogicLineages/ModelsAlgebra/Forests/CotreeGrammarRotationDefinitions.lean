module
public import LogicLineages.ModelsAlgebra.Forests.CotreeGrammarOpenDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreeGrammarRotation
open CotreeGrammarOpen CotreeGrammarFlow

def compose {Q : Type} {δ : Q → Q → Q} {r q s}
    (C : Context δ r q) (D : Context δ q s) : Context δ r s :=
  match C with
  | .hole _ => D
  | .left C t => .left (compose C D) t
  | .right t C => .right t (compose C D)

def contextHoles {Q : Type} {δ : Q → Q → Q} {r q} : Context δ r q → List Q
  | .hole _ => []
  | .left C t => contextHoles C ++ holes t
  | .right t C => holes t ++ contextHoles C

/-- Two independently distinguished, ordered holes. The fork constructors
retain which actual branch contains each hole; remaining siblings are genuine trees. -/
inductive TwoContext {Q : Type} (δ : Q → Q → Q) : Q → Q → Q → Type where
  | fork {r s x y} : Context δ r x → Context δ s y → TwoContext δ (δ r s) x y
  | forkSwap {r s x y} : Context δ r y → Context δ s x → TwoContext δ (δ r s) x y
  | left {r s x y} : TwoContext δ r x y → Tree δ s → TwoContext δ (δ r s) x y
  | right {r s x y} : Tree δ r → TwoContext δ s x y → TwoContext δ (δ r s) x y

def fill {Q : Type} {δ : Q → Q → Q} {r x y} (C : TwoContext δ r x y)
    (u : Tree δ x) (v : Tree δ y) : Tree δ r :=
  match C with
  | .fork C D => .branch (plug C u) (plug D v)
  | .forkSwap C D => .branch (plug C v) (plug D u)
  | .left C t => .branch (fill C u v) t
  | .right t C => .branch t (fill C u v)

def twoHoles {Q : Type} {δ : Q → Q → Q} {r x y} : TwoContext δ r x y → List Q
  | .fork C D => contextHoles C ++ contextHoles D
  | .forkSwap C D => contextHoles C ++ contextHoles D
  | .left C t => twoHoles C ++ holes t
  | .right t C => holes t ++ twoHoles C

def twoCounts {Q : Type} [DecidableEq Q] {δ : Q → Q → Q} {r x y}
    (C : TwoContext δ r x y) : Counts Q := counts (fill C (.hole x) (.hole y))

/-- Actual occurrence of a nonterminal at a node, including expanded nodes. -/
inductive Occurs {Q : Type} {δ : Q → Q → Q} (x : Q) : {q : Q} → Tree δ q → Prop where
  | root (t : Tree δ x) : Occurs x t
  | left {r s} {l : Tree δ r} {t : Tree δ s} : Occurs x l → Occurs x (.branch l t)
  | right {r s} {l : Tree δ r} {t : Tree δ s} : Occurs x t → Occurs x (.branch l t)

end LogicLineages.ModelsAlgebra.Forests.CotreeGrammarRotation
