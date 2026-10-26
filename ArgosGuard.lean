/-
  Argos: guarded revocation on a Fabric VDR (first model).

  Abstraction level:
  * World state: one version number per registry key. Values are abstracted
    away; every committed write bumps the version of the written key.
    (Fabric versions are (blockNum, txNum) pairs; only their strict
    monotonicity is used here, so `Nat` is enough.)
  * A transaction carries the read set produced at endorsement
    (key, version observed) and its write set.
  * Validation is sequential MVCC over the ordered transaction stream:
    blocks are concatenated, and within a block a transaction is validated
    against the writes of the valid transactions before it.
  * Ordering is given. Censorship, front-running and reordering by the
    ordering service are out of scope: every theorem holds for every order.
  * The endorsement step is not modelled here: `MutuallyGuarded` takes as a
    hypothesis that the pinned guard versions are in the read set. In the
    chaincode this link is made by the endorsement-time comparison
    (FAILED_PRECONDITION); `ArgosGuardExt.lean` models that step and derives
    `MutuallyGuarded` as a theorem (`mutuallyGuarded_of_endorse`).

  Lean 4 core only, no Mathlib. Build: `lake build`.
-/

namespace Argos

abbrev Key := Nat
abbrev Version := Nat
abbrev State := Key → Version

structure Tx where
  id     : Nat
  reads  : List (Key × Version)
  writes : List Key
deriving DecidableEq, Repr

/-- MVCC check: every key in the read set still has the version seen at endorsement. -/
def readsOk (s : State) (t : Tx) : Bool :=
  t.reads.all fun r => s r.1 == r.2

/-- Effect of a committed transaction: every written key gets a new version. -/
def apply (s : State) (t : Tx) : State :=
  fun k => if k ∈ t.writes then s k + 1 else s k

def step (s : State) (t : Tx) : State :=
  if readsOk s t then apply s t else s

/-- World state after validating the stream. -/
def final : State → List Tx → State
  | s, [] => s
  | s, t :: ts => final (step s t) ts

/-- Transactions marked VALID, in commit order. -/
def committed : State → List Tx → List Tx
  | _, [] => []
  | s, t :: ts =>
    if readsOk s t then t :: committed (apply s t) ts
    else committed s ts

/-! ## Basic lemmas -/

theorem readsOk_spec {s : State} {t : Tx} (h : readsOk s t = true) :
    ∀ r ∈ t.reads, s r.1 = r.2 := by
  intro r hr
  have := List.all_eq_true.mp h r hr
  simpa using this

theorem readsOk_of_all {s : State} {t : Tx} (h : ∀ r ∈ t.reads, s r.1 = r.2) :
    readsOk s t = true := by
  unfold readsOk
  rw [List.all_eq_true]
  intro r hr
  simp [h r hr]

theorem apply_mono (s : State) (t : Tx) (k : Key) : s k ≤ apply s t k := by
  unfold apply
  split
  · exact Nat.le_succ _
  · exact Nat.le_refl _

theorem apply_write (s : State) (t : Tx) (k : Key) (h : k ∈ t.writes) :
    s k < apply s t k := by
  simp [apply, h]

theorem step_mono (s : State) (t : Tx) (k : Key) : s k ≤ step s t k := by
  unfold step
  split
  · exact apply_mono s t k
  · exact Nat.le_refl _

/-- Versions never decrease. -/
theorem final_mono : ∀ (ts : List Tx) (s : State) (k : Key), s k ≤ final s ts k
  | [], _, _ => Nat.le_refl _
  | t :: ts, s, k => Nat.le_trans (step_mono s t k) (final_mono ts (step s t) k)

/-- Once a key has moved past the version a transaction read, that
transaction can never commit, whatever comes after. -/
theorem stale_never_commits (t : Tx) (k : Key) (v : Version) (hr : (k, v) ∈ t.reads) :
    ∀ (ts : List Tx) (s : State), v < s k → t ∉ committed s ts
  | [], _, _ => by simp [committed]
  | u :: ts, s, hv => by
    unfold committed
    split
    · next hok =>
      intro hmem
      cases List.mem_cons.mp hmem with
      | inl heq =>
        subst heq
        have := readsOk_spec hok (k, v) hr
        simp at this
        rw [this] at hv
        exact Nat.lt_irrefl _ hv
      | inr hin =>
        exact stale_never_commits t k v hr ts (apply s u)
          (Nat.lt_of_lt_of_le hv (apply_mono s u k)) hin
    · exact stale_never_commits t k v hr ts s hv

/-! ## Property 1: at most one of two mutually guarded revocations commits -/

/-- `t₁` revokes in registry `a` and guards registry `b` at version `vb`;
`t₂` revokes in `b` and guards `a` at version `va`. -/
structure MutuallyGuarded (t₁ t₂ : Tx) (a b : Key) (va vb : Version) : Prop where
  ne : t₁ ≠ t₂
  w₁ : a ∈ t₁.writes
  w₂ : b ∈ t₂.writes
  g₁ : (b, vb) ∈ t₁.reads
  g₂ : (a, va) ∈ t₂.reads

/-- For every transaction stream (any order, any other transactions mixed in),
starting from any state no older than the one the guards refer to, the two
mutually guarded revocations do not both commit. -/
theorem at_most_one {t₁ t₂ : Tx} {a b : Key} {va vb : Version}
    (hg : MutuallyGuarded t₁ t₂ a b va vb) :
    ∀ (ts : List Tx) (s : State), va ≤ s a → vb ≤ s b →
      ¬ (t₁ ∈ committed s ts ∧ t₂ ∈ committed s ts)
  | [], _, _, _ => by simp [committed]
  | u :: ts, s, ha, hb => by
    unfold committed
    split
    · next hok =>
      intro ⟨h₁, h₂⟩
      by_cases hu₁ : u = t₁
      · subst hu₁
        cases List.mem_cons.mp h₂ with
        | inl heq => exact hg.ne heq.symm
        | inr hin =>
          exact stale_never_commits t₂ a va hg.g₂ ts (apply s _)
            (Nat.lt_of_le_of_lt ha (apply_write s _ a hg.w₁)) hin
      · by_cases hu₂ : u = t₂
        · subst hu₂
          cases List.mem_cons.mp h₁ with
          | inl heq => exact hg.ne heq
          | inr hin =>
            exact stale_never_commits t₁ b vb hg.g₁ ts (apply s _)
              (Nat.lt_of_le_of_lt hb (apply_write s _ b hg.w₂)) hin
        · have h₁' : t₁ ∈ committed (apply s u) ts := by
            cases List.mem_cons.mp h₁ with
            | inl heq => exact absurd heq.symm hu₁
            | inr hin => exact hin
          have h₂' : t₂ ∈ committed (apply s u) ts := by
            cases List.mem_cons.mp h₂ with
            | inl heq => exact absurd heq.symm hu₂
            | inr hin => exact hin
          exact at_most_one hg ts (apply s u)
            (Nat.le_trans ha (apply_mono s u a))
            (Nat.le_trans hb (apply_mono s u b)) ⟨h₁', h₂'⟩
    · exact at_most_one hg ts s ha hb

/-- The TOCTOU scenario: both verifiers checked the same state `s₀`. -/
theorem at_most_one_from_checked_state {t₁ t₂ : Tx} {a b : Key} (s₀ : State)
    (hg : MutuallyGuarded t₁ t₂ a b (s₀ a) (s₀ b)) (ts : List Tx) :
    ¬ (t₁ ∈ committed s₀ ts ∧ t₂ ∈ committed s₀ ts) :=
  at_most_one hg ts s₀ (Nat.le_refl _) (Nat.le_refl _)

/-! ## Property 2: a rejected revocation is detectable

If `t` was endorsed against a state no newer than the current one and it
does not commit, then some registry in its read set has been written since
the version it saw. The rejected party learns that "someone did something". -/

theorem rejected_detectable (t : Tx) :
    ∀ (ts : List Tx) (s : State), (∀ r ∈ t.reads, r.2 ≤ s r.1) →
      t ∈ ts → t ∉ committed s ts → ∃ r ∈ t.reads, r.2 < final s ts r.1
  | [], _, _, hmem, _ => by simp at hmem
  | u :: ts, s, hle, hmem, hnot => by
    simp only [final]
    unfold committed at hnot
    split at hnot
    · next hok =>
      have hstep : step s u = apply s u := by simp [step, hok]
      rw [hstep]
      have hne : t ≠ u := fun h => hnot (h ▸ List.mem_cons_self ..)
      have hin : t ∈ ts := by
        cases List.mem_cons.mp hmem with
        | inl heq => exact absurd heq hne
        | inr hin => exact hin
      have hnot' : t ∉ committed (apply s u) ts := fun h => hnot (List.mem_cons_of_mem _ h)
      exact rejected_detectable t ts (apply s u)
        (fun r hr => Nat.le_trans (hle r hr) (apply_mono s u r.1)) hin hnot'
    · next hok =>
      have hstep : step s u = s := by simp [step, hok]
      rw [hstep]
      by_cases htu : t = u
      · subst htu
        have hall : ¬ ∀ r ∈ t.reads, s r.1 = r.2 := fun h => by
          rw [readsOk_of_all h] at hok
          exact hok rfl
        simp only [Classical.not_forall] at hall
        obtain ⟨r, hr, hne⟩ := hall
        have hlt : r.2 < s r.1 := Nat.lt_of_le_of_ne (hle r hr) (fun h => hne h.symm)
        exact ⟨r, hr, Nat.lt_of_lt_of_le hlt (final_mono ts s r.1)⟩
      · have hin : t ∈ ts := by
          cases List.mem_cons.mp hmem with
          | inl heq => exact absurd heq htu
          | inr hin => exact hin
        exact rejected_detectable t ts s hle hin hnot

/-! ## Property 3: without guards the gap is real (B1u)

The "check" of the other registry is a client-side query, so it is not in
the read set. Each revocation reads only its own registry. From the state
both verifiers checked, both commit, in either order. -/

def unguarded (id : Nat) (s : State) (x : Key) : Tx :=
  { id := id, reads := [(x, s x)], writes := [x] }

theorem b1u_both_commit (s : State) (a b : Key) (hab : a ≠ b) :
    committed s [unguarded 1 s a, unguarded 2 s b]
      = [unguarded 1 s a, unguarded 2 s b] := by
  have hba : b ≠ a := fun h => hab h.symm
  simp [committed, readsOk, unguarded, apply, hba]

/-! ## Concrete instance mirroring the B1 / B1u measurement -/

namespace Example

def a : Key := 1
def b : Key := 2
def s₀ : State := fun _ => 3

/-- Guarded (B1): each revocation reads its own registry (own CAS) and the other one. -/
def t₁ : Tx := { id := 1, reads := [(a, 3), (b, 3)], writes := [a] }
def t₂ : Tx := { id := 2, reads := [(b, 3), (a, 3)], writes := [b] }

/-- Unguarded (B1u). -/
def t₁u : Tx := { id := 1, reads := [(a, 3)], writes := [a] }
def t₂u : Tx := { id := 2, reads := [(b, 3)], writes := [b] }

-- B1: VALID + MVCC_READ_CONFLICT, in either order.
example : committed s₀ [t₁, t₂] = [t₁] := by decide
example : committed s₀ [t₂, t₁] = [t₂] := by decide
-- B1u: VALID + VALID.
example : committed s₀ [t₁u, t₂u] = [t₁u, t₂u] := by decide

example : MutuallyGuarded t₁ t₂ a b (s₀ a) (s₀ b) :=
  { ne := by decide, w₁ := by decide, w₂ := by decide, g₁ := by decide, g₂ := by decide }

end Example

end Argos
