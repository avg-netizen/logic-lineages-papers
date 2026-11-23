# Paper 16: actual same-body rank p selection and typed tuple reconstruction

Original (T): `16-persistent-marking-termination-ordering/sections/ordinals.tex:113–127`.
Source-only, pending native. This is independent of the eventual
choice/numerical calibration of the actual neutral rank.

`selectRankInputs i g v` changes only the application leaf, literally
to `rankApplication i g v.applicationGuard`. It retains all other
physical leaves, in particular the same original chosenA. A genuine
`RankApplicationFit` must calibrate the *new* program at every original
raw (f,u,y) to the unchanged graph for given s; no inference of this
fit from the old scalar or p fits, and no import of fixed Settings.

Actual arithmetic output forget from
`exact_OpenRankApplicationForgets` gives old p on the identical tape
in the same body. Consequently original uniqueness and input guards
are obtained for new p. The actual old-body Evaluates, Interprets and
Rules are unchanged. The new actual chosenH is rerun with the new p:
numeric calibration, true closed typed totality, genuine literal
parsed proof and same-input/output alignment are rederived, not
renamed from old h. `ExactNeutralRankApplicationReselect` takes the
held prior tuple; `ExactNeutralRankApplicationReinstall` may instead
start directly from its original base facts, so it does not require
old h or old totality.

This does not change the rank definitions or switch r/ID₁ bodies.
If a later caller installs r = rankEven, that exact body’s lawful base
facts/tuple must independently be supplied. RankDrop, rank totality,
neutral coverage, numeric feasibility, ForwardRule and all-type C→I
are not consequences of this generic installation.

Serial proof root `NumberedWindowInternalNeutralRankApplicationReinstallProof`
(1763 local/33 external; targets 877/29) after RankGuardForgetsProof.
Linarith on the same pinned original typed calibration dependency;
no Hydra, Sym2, GameAdd or Rank imports in the source closure.

Current source and premise pins (SHA256):
~~~text
393b794811881290eadb135942515250441fe9c1b1cc993e98b77c4d6a92d895  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalNeutralRankApplicationReinstallTargets.lean
06e9a455d5a6a38df476000172bc69037cd98bb086a9934fcc96bd6d83051c0b  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalNeutralRankApplicationReinstallProof.lean
380469ddfb9d660fba1e083bc5a637cb3fa69178e56808a228d7a08aa46f73c4  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalNeutralRankGuardDefinitions.lean
093a823b472ecf248610319fa89dda122253578977a45eb1569b7ef51dade276  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalNeutralRankGuardForgetsProof.lean
e9ab46ffb99b8fb210961721c3b86eeb82cff7c5a7fa0214b334785d70ae13e6  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalApplicationOutputGuardReinstallProof.lean
526aa249902b4e4bf00f45bee770bdcdc9f9b39c2dc341778834600b7f8bf1b5  16-persistent-marking-termination-ordering/sections/ordinals.tex
~~~
