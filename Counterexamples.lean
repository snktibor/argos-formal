/-
  Counterexamples showing that each mutation of `ArgosGuard.lean`
  does not merely break the proofs but makes the *statement* false, plus the
  sharpness witnesses ("exactly one" is not provable) and non-vacuity witnesses.
  Self-contained copies of the mutated definitions carry the mutation number.
  Build: `lake build` (Lean 4.23.0, core only).
-/
import ArgosGuard
import ArgosToctou
namespace Argos.Review

open Argos

-- Shared fixtures: two registries, both at version 3 in the checked state.
def a : Key := 1
def b : Key := 2
def s₀ : State := fun _ => 3

/-! ### M1 / M2: one side does not guard (field `g₁` resp. `g₂` dropped).
With the ORIGINAL semantics, if `t₁` does not read `b`, then in the order
`[t₂, t₁]` both commit. So `at_most_one` is false without `g₁`. -/
def t₁_noguard : Tx := { id := 1, reads := [(a, 3)], writes := [a] }
def t₂_guarded : Tx := { id := 2, reads := [(b, 3), (a, 3)], writes := [b] }

theorem ce_M1 : committed s₀ [t₂_guarded, t₁_noguard] = [t₂_guarded, t₁_noguard] := by decide
-- Everything else in `MutuallyGuarded` holds for this pair except `g₁`:
example : t₁_noguard ≠ t₂_guarded := by decide
example : a ∈ t₁_noguard.writes := by decide
example : b ∈ t₂_guarded.writes := by decide
example : (a, 3) ∈ t₂_guarded.reads := by decide
example : (b, 3) ∉ t₁_noguard.reads := by decide

/-! ### M3: `committed` ignores the read set. -/
def committed₃ : State → List Tx → List Tx
  | _, [] => []
  | s, t :: ts => t :: committed₃ (apply s t) ts

theorem ce_M3 : committed₃ s₀ [Example.t₁, Example.t₂] = [Example.t₁, Example.t₂] := by decide

/-! ### M4: a committed write does not bump the version. -/
def apply₄ (s : State) (_t : Tx) : State := s
def committed₄ : State → List Tx → List Tx
  | _, [] => []
  | s, t :: ts => if readsOk s t then t :: committed₄ (apply₄ s t) ts else committed₄ s ts

theorem ce_M4 : committed₄ s₀ [Example.t₁, Example.t₂] = [Example.t₁, Example.t₂] := by decide

/-! ### M5: the MVCC check accepts stale reads (`≤` instead of `=`). -/
def readsOk₅ (s : State) (t : Tx) : Bool := t.reads.all fun r => decide (r.2 ≤ s r.1)
def committed₅ : State → List Tx → List Tx
  | _, [] => []
  | s, t :: ts => if readsOk₅ s t then t :: committed₅ (apply s t) ts else committed₅ s ts

theorem ce_M5 : committed₅ s₀ [Example.t₁, Example.t₂] = [Example.t₁, Example.t₂] := by decide

/-! ### M6: the freshness hypothesis `va ≤ s a` dropped.
ORIGINAL semantics. `t₂` pins `a` at a *future* version 4 while the state
is at 3. `t₁` commits, bumps `a` to 4, and then `t₂` commits too.
So `va ≤ s a` is necessary: a guard pinned to a version the verifier could
not have observed turns the guard into "wait until the other side revoked". -/
def t₂_future : Tx := { id := 2, reads := [(b, 3), (a, 4)], writes := [b] }

theorem ce_M6_mutually_guarded : MutuallyGuarded Example.t₁ t₂_future a b 4 3 :=
  { ne := by decide, w₁ := by decide, w₂ := by decide, g₁ := by decide, g₂ := by decide }
theorem ce_M6 : committed s₀ [Example.t₁, t₂_future] = [Example.t₁, t₂_future] := by decide
example : ¬ (4 ≤ s₀ a) := by decide

/-! ### M7: `ne` dropped. One transaction that writes both registries and
reads both satisfies the remaining fields with `t₁ = t₂`, and trivially
"both" commit. -/
def t_both : Tx := { id := 7, reads := [(a, 3), (b, 3)], writes := [a, b] }
theorem ce_M7 : t_both ∈ committed s₀ [t_both] ∧ t_both ∈ committed s₀ [t_both] := by decide

/-! ### M8: no intra-block sequencing — every transaction of the stream is
validated against the state at the start of the stream. -/
def committed₈ : State → List Tx → List Tx
  | _, [] => []
  | s, t :: ts => if readsOk s t then t :: committed₈ s ts else committed₈ s ts

theorem ce_M8 : committed₈ s₀ [Example.t₁, Example.t₂] = [Example.t₁, Example.t₂] := by decide

/-! ### Sharpness: "exactly one" is NOT provable.
A third, independent write to both registries ahead of the pair makes both
guarded revocations fail. An independent write to `a` alone decides who wins
purely by position. -/
def w_ab : Tx := { id := 9, reads := [], writes := [a, b] }
theorem ce_neither_commits : committed s₀ [w_ab, Example.t₁, Example.t₂] = [w_ab] := by decide

def w_a : Tx := { id := 9, reads := [], writes := [a] }
theorem ce_order_decides_1 : committed s₀ [w_a, Example.t₁, Example.t₂] = [w_a] := by decide
theorem ce_order_decides_2 : committed s₀ [Example.t₁, w_a, Example.t₂] = [Example.t₁, w_a] := by decide
theorem ce_order_decides_3 : committed s₀ [Example.t₂, w_a, Example.t₁] = [Example.t₂, w_a] := by decide

/-! ### Non-vacuity witnesses for the hypotheses of the main theorems. -/
example : MutuallyGuarded Example.t₁ Example.t₂ a b (s₀ a) (s₀ b) :=
  { ne := by decide, w₁ := by decide, w₂ := by decide, g₁ := by decide, g₂ := by decide }
-- each side CAN commit (the conclusion is not vacuous):
example : Example.t₁ ∈ committed s₀ [Example.t₁, Example.t₂] := by decide
example : Example.t₂ ∈ committed s₀ [Example.t₂, Example.t₁] := by decide
-- `rejected_detectable` hypotheses are simultaneously satisfiable:
example : Example.t₂ ∈ [Example.t₁, Example.t₂] ∧ Example.t₂ ∉ committed s₀ [Example.t₁, Example.t₂]
    ∧ ∀ r ∈ Example.t₂.reads, r.2 ≤ s₀ r.1 := by decide

/-! ### M9 / M10: hypotheses of `no_bifurcation` (`ArgosToctou.lean`).
Fixture: `ToctouExample` (A revokes `(a, 0)`, B revokes `(b, 0)`, both checked
the empty prefix, i.e. state `s₀`). -/
open ToctouExample in
section

/-- M9: A does not guard `b` (field `guarded` dropped). Every other field of A's
step holds, and in the order `[t₂, t₁u]` both revocations commit. -/
def cA_noguard : GuardedCall := ⟨1, a, []⟩

example : endorse s₀ cA_noguard = some Example.t₁u := by decide
example : ¬ revokedAt rev R₀ s₀ [] (b, 0) := by simp [revokedAt, R₀, committed]
example : (a, 0) ∈ rev Example.t₁u := by decide
example : ¬ ∃ v, (b, v) ∈ cA_noguard.guards := by simp [cA_noguard]
theorem ce_M9 : readsOk s₀ Example.t₂ = true ∧
    readsOk (final s₀ [Example.t₂]) Example.t₁u = true := by decide

/-- M10: B pins `a` at the version of a LATER read (after A's revocation
committed), not at the version of its check (field `pinned` dropped). The call
is endorsed against that later state, and both revocations commit. -/
def cB_latePin : GuardedCall := ⟨2, b, [(a, 4)]⟩
def t₂_late : Tx := { id := 2, reads := [(b, 3), (a, 4)], writes := [b] }

example : endorse (final s₀ [Example.t₁]) cB_latePin = some t₂_late := by decide
example : ¬ revokedAt rev R₀ s₀ [] (a, 0) := by simp [revokedAt, R₀, committed]
example : (b, 0) ∈ rev t₂_late := by decide
example : (a, 4) ∈ cB_latePin.guards ∧ final s₀ [] a ≠ 4 := by decide
theorem ce_M10 : readsOk s₀ Example.t₁ = true ∧
    readsOk (final s₀ [Example.t₁]) t₂_late = true := by decide

end

end Argos.Review
