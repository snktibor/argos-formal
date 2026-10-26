/-
  Extensions on top of `ArgosGuard.lean` (imported, unchanged). Lean 4.23.0, core only. Build: `lake build`.

  Contents
  1. `committed_append`, `final_append`: the stream can be split at any position.
  2. `version_grows_has_writer`: a version only grows through a committed writer.
  3. `rejected_has_prior_committed_writer`: strengthened detectability — a
     rejected transaction's read key was written by a transaction that
     COMMITTED EARLIER in the same stream (not just "the version is higher
     at the end").
  4. `guard_excludes_prior_writer`: the one-sided guard theorem. Only `t₂`
     guards `a`; if `t₂` commits then no writer of `a` committed before it.
     `at_most_one` is a corollary.
  5. `pair_alone_exactly_one`: in the absence of any other transaction, and
     with `t₁` endorsed against exactly the start state, the first of the two
     commits and the second is rejected ("exactly one" holds only here).
  6. A minimal model of the chaincode's endorsement step
     (`updateRevRegEntryIfGuardsUnchanged`): `endorse` reads the target and
     every guard inside the transaction and refuses (FAILED_PRECONDITION)
     when a guard's current version differs from the pinned one. From this,
     `MutuallyGuarded` becomes a THEOREM (`mutuallyGuarded_of_endorse`)
     instead of a hypothesis, and the freshness side conditions of
     `at_most_one` follow from "endorsement state ≼ validation start state".
-/
import ArgosGuard
namespace Argos

/-! ## 1. Splitting the stream -/

theorem final_append (s : State) (l₁ l₂ : List Tx) :
    final s (l₁ ++ l₂) = final (final s l₁) l₂ := by
  induction l₁ generalizing s with
  | nil => rfl
  | cons t l ih => simp only [List.cons_append, final]; exact ih _

theorem committed_append (s : State) (l₁ l₂ : List Tx) :
    committed s (l₁ ++ l₂) = committed s l₁ ++ committed (final s l₁) l₂ := by
  induction l₁ generalizing s with
  | nil => rfl
  | cons t l ih =>
    simp only [List.cons_append, committed, final, step]
    cases readsOk s t <;> simp [ih]

theorem mem_committed_of_mem_prefix {s : State} {l₁ l₂ : List Tx} {t : Tx}
    (h : t ∈ committed s l₁) : t ∈ committed s (l₁ ++ l₂) := by
  rw [committed_append]; exact List.mem_append_left _ h

theorem final_eq_of_readsOk_false {s : State} {t : Tx} (h : readsOk s t = false) :
    step s t = s := by
  simp [step, h]

/-! ## 2. A version grows only through a committed writer -/

theorem version_grows_has_writer :
    ∀ (ts : List Tx) (s : State) (k : Key), s k < final s ts k →
      ∃ u ∈ committed s ts, k ∈ u.writes
  | [], s, k, h => absurd h (Nat.lt_irrefl _)
  | u :: ts, s, k, h => by
    simp only [final, committed] at *
    unfold step at h
    split at h
    · next hok =>
      rw [if_pos hok]
      by_cases hk : k ∈ u.writes
      · exact ⟨u, List.mem_cons_self .., hk⟩
      · have heq : apply s u k = s k := by simp [apply, hk]
        rw [← heq] at h
        obtain ⟨w, hw, hkw⟩ := version_grows_has_writer ts (apply s u) k h
        exact ⟨w, List.mem_cons_of_mem _ hw, hkw⟩
    · next hok =>
      rw [if_neg hok]
      exact version_grows_has_writer ts s k h

/-- Conversely, a committed writer strictly bumps the key over the whole stream. -/
theorem writer_bumps :
    ∀ (ts : List Tx) (s : State) (u : Tx) (k : Key),
      u ∈ committed s ts → k ∈ u.writes → s k < final s ts k
  | [], _, _, _, h, _ => by simp [committed] at h
  | v :: ts, s, u, k, h, hk => by
    simp only [committed] at h
    simp only [final]
    split at h
    · next hok =>
      have hstep : step s v = apply s v := by simp [step, hok]
      rw [hstep]
      cases List.mem_cons.mp h with
      | inl heq =>
        subst heq
        exact Nat.lt_of_lt_of_le (apply_write s u k hk) (final_mono ts _ k)
      | inr hin =>
        exact Nat.lt_of_le_of_lt (apply_mono s v k) (writer_bumps ts (apply s v) u k hin hk)
    · next hok =>
      have hstep : step s v = s := by simp [step, hok]
      rw [hstep]
      exact writer_bumps ts s u k h hk

/-! ## 3. Strengthened detectability -/

/-- If `t` sits at a position of the stream (`pre ++ t :: post`), was endorsed
against exactly the state `s` the stream starts from (the TOCTOU scenario:
`s` is the state the verifier checked), and does not commit, then some key of
its read set was written by a transaction that **committed in `pre`**, i.e.
before `t` was validated. This is the formal shape of "the rejected party knows
that someone wrote before them". (With only `r.2 ≤ s r.1` the writer may lie
before the start of the modelled stream; then the conclusion weakens to
`r.2 < s r.1 ∨ ∃ u ∈ committed s pre, r.1 ∈ u.writes`.) -/
theorem rejected_has_prior_committed_writer (t : Tx) (pre post : List Tx) (s : State)
    (hfresh : ∀ r ∈ t.reads, r.2 = s r.1)
    (hnot : t ∉ committed s (pre ++ t :: post)) :
    ∃ r ∈ t.reads, ∃ u ∈ committed s pre, r.1 ∈ u.writes := by
  rw [committed_append] at hnot
  have hnot₂ : t ∉ committed (final s pre) (t :: post) :=
    fun h => hnot (List.mem_append_right _ h)
  have hfail : readsOk (final s pre) t = false := by
    cases hok : readsOk (final s pre) t with
    | true => exact absurd (by simp [committed, hok]) hnot₂
    | false => rfl
  -- some read is off; it can only be strictly behind, by monotonicity
  have hall : ¬ ∀ r ∈ t.reads, final s pre r.1 = r.2 := fun h => by
    rw [readsOk_of_all h] at hfail; cases hfail
  simp only [Classical.not_forall] at hall
  obtain ⟨r, hr, hne⟩ := hall
  have hge : r.2 ≤ final s pre r.1 := (hfresh r hr) ▸ final_mono pre s r.1
  have hlt : r.2 < final s pre r.1 := Nat.lt_of_le_of_ne hge (fun h => hne h.symm)
  -- and strictly behind means: the version grew along `pre`
  have hgrow : s r.1 < final s pre r.1 := (hfresh r hr) ▸ hlt
  obtain ⟨u, hu, hw⟩ := version_grows_has_writer pre s r.1 hgrow
  exact ⟨r, hr, u, hu, hw⟩

/-! ## 4. The one-sided guard -/

/-- Only `t₂` guards `a` (at version `va`, no newer than the start state).
If `t₂` commits at its position, then no transaction writing `a` committed
before it. Mutual guarding is not needed for this direction. -/
theorem guard_excludes_prior_writer {t₂ : Tx} {a : Key} {va : Version}
    (hg : (a, va) ∈ t₂.reads) (pre post : List Tx) (s : State) (ha : va ≤ s a)
    (hc : t₂ ∈ committed (final s pre) (t₂ :: post)) :
    ∀ u ∈ committed s pre, a ∉ u.writes := by
  intro u hu hw
  have hbump := writer_bumps pre s u a hu hw
  -- t₂ commits at the head of its suffix, so its reads match `final s pre`
  have hok : readsOk (final s pre) t₂ = true := by
    cases hok : readsOk (final s pre) t₂ with
    | true => rfl
    | false => simp [committed, hok] at hc; exact absurd hc (by
        intro h
        exact stale_never_commits t₂ a va hg post (final s pre)
          (Nat.lt_of_le_of_lt ha hbump) h)
  have := readsOk_spec hok (a, va) hg
  simp at this
  -- `va = final s pre a`, but `va ≤ s a < final s pre a`
  rw [this] at hbump
  exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt ha hbump)

/-- `at_most_one` re-derived from the one-sided theorem, for the case where
the stream is split explicitly at `t₂`'s committing position. -/
theorem at_most_one_via_one_sided {t₁ t₂ : Tx} {a b : Key} {va vb : Version}
    (hg : MutuallyGuarded t₁ t₂ a b va vb) (pre post : List Tx) (s : State)
    (ha : va ≤ s a)
    (hc₂ : t₂ ∈ committed (final s pre) (t₂ :: post)) :
    t₁ ∉ committed s pre :=
  fun h₁ => guard_excludes_prior_writer hg.g₂ pre post s ha hc₂ t₁ h₁ hg.w₁

/-! ## 5. The isolated pair: exactly one -/

theorem readsOk_false_of_moved {s : State} {t : Tx} {k : Key} {v : Version}
    (hr : (k, v) ∈ t.reads) (hne : s k ≠ v) : readsOk s t = false := by
  cases hok : readsOk s t with
  | false => rfl
  | true =>
    have := readsOk_spec hok (k, v) hr
    simp at this
    exact absurd this hne

/-- Nobody else in the stream, `t₁` endorsed against exactly `s₀`, mutually
guarded: `t₁` commits and `t₂` is rejected. By symmetry (swap the roles) the
second one in the order is always the loser. -/
theorem pair_alone_exactly_one {t₁ t₂ : Tx} {a b : Key} (s₀ : State)
    (hg : MutuallyGuarded t₁ t₂ a b (s₀ a) (s₀ b))
    (hfresh : ∀ r ∈ t₁.reads, s₀ r.1 = r.2) :
    committed s₀ [t₁, t₂] = [t₁] := by
  have h₁ : readsOk s₀ t₁ = true := readsOk_of_all hfresh
  have h₂ : readsOk (apply s₀ t₁) t₂ = false :=
    readsOk_false_of_moved hg.g₂ (Nat.ne_of_gt (apply_write s₀ t₁ a hg.w₁))
  simp [committed, h₁, h₂]

/-! ## 6. A minimal model of the chaincode's endorsement step -/

/-- A client call of `updateRevRegEntryIfGuardsUnchanged`: the target entry
and the guards `(revRegDefId, expectedVersion)`. Values are abstracted away. -/
structure GuardedCall where
  id      : Nat
  target  : Key
  guards  : List (Key × Version)
deriving DecidableEq, Repr

/-- The guards other than the target itself; a self-guard is answered from the
record already loaded for the target and issues no second read
(`readGuardedVersion` in `RevRegEntryService`). -/
def GuardedCall.otherGuards (c : GuardedCall) : List (Key × Version) :=
  c.guards.filter (fun g => g.1 != c.target)

/-- Endorsement against peer state `s`. The chaincode reads the target (owner
check) and each other guard inside the transaction, so each of them enters the
read set with the version the peer has. If any guard differs from the pinned
version it throws `FAILED_PRECONDITION` and no transaction is produced. -/
def endorse (s : State) (c : GuardedCall) : Option Tx :=
  if c.guards.all (fun g => s g.1 == g.2) then
    some { id := c.id
         , reads := (c.target, s c.target) :: c.otherGuards.map (fun g => (g.1, s g.1))
         , writes := [c.target] }
  else none

/-- The unguarded path (`updateRevRegEntry`): only the target is read. -/
def endorseUnguarded (s : State) (c : GuardedCall) : Tx :=
  { id := c.id, reads := [(c.target, s c.target)], writes := [c.target] }

theorem endorse_some_guards_hold {s : State} {c : GuardedCall} {t : Tx}
    (h : endorse s c = some t) : ∀ g ∈ c.guards, s g.1 = g.2 := by
  unfold endorse at h
  split at h
  · next hall =>
    intro g hg
    have := List.all_eq_true.mp hall g hg
    simpa using this
  · cases h

theorem endorse_some_tx {s : State} {c : GuardedCall} {t : Tx}
    (h : endorse s c = some t) :
    t = { id := c.id
        , reads := (c.target, s c.target) :: c.otherGuards.map (fun g => (g.1, s g.1))
        , writes := [c.target] } := by
  unfold endorse at h
  split at h
  · exact (Option.some.inj h).symm
  · cases h

/-- Every pinned guard `(k, v)` is in the read set **with the pinned version**:
this is the link between the verifier's observation and the MVCC read set,
and it is exactly what the endorsement-time comparison buys. -/
theorem endorse_reads_guard {s : State} {c : GuardedCall} {t : Tx}
    (h : endorse s c = some t) {k : Key} {v : Version} (hg : (k, v) ∈ c.guards) :
    (k, v) ∈ t.reads := by
  have hv : s k = v := endorse_some_guards_hold h (k, v) hg
  rw [endorse_some_tx h]
  by_cases hk : k = c.target
  · subst hk; rw [← hv]; exact List.mem_cons_self ..
  · apply List.mem_cons_of_mem
    rw [List.mem_map]
    refine ⟨(k, v), ?_, by simp [hv]⟩
    rw [GuardedCall.otherGuards, List.mem_filter]
    exact ⟨hg, by simpa using hk⟩

theorem endorse_writes_target {s : State} {c : GuardedCall} {t : Tx}
    (h : endorse s c = some t) : c.target ∈ t.writes := by
  rw [endorse_some_tx h]; simp

theorem endorse_reads_target {s : State} {c : GuardedCall} {t : Tx}
    (h : endorse s c = some t) : (c.target, s c.target) ∈ t.reads := by
  rw [endorse_some_tx h]; simp

theorem endorse_id {s : State} {c : GuardedCall} {t : Tx}
    (h : endorse s c = some t) : t.id = c.id := by
  rw [endorse_some_tx h]

/-- `MutuallyGuarded` is now a theorem: two calls with distinct ids that pin
each other's target, both successfully endorsed (possibly on different peers
and against different states), yield a mutually guarded pair. -/
theorem mutuallyGuarded_of_endorse {s₁ s₂ : State} {c₁ c₂ : GuardedCall} {t₁ t₂ : Tx}
    {va vb : Version}
    (h₁ : endorse s₁ c₁ = some t₁) (h₂ : endorse s₂ c₂ = some t₂)
    (hid : c₁.id ≠ c₂.id)
    (hg₁ : (c₂.target, vb) ∈ c₁.guards) (hg₂ : (c₁.target, va) ∈ c₂.guards) :
    MutuallyGuarded t₁ t₂ c₁.target c₂.target va vb where
  ne := fun h => hid (by rw [← endorse_id h₁, ← endorse_id h₂, h])
  w₁ := endorse_writes_target h₁
  w₂ := endorse_writes_target h₂
  g₁ := endorse_reads_guard h₁ hg₁
  g₂ := endorse_reads_guard h₂ hg₂

/-- The pinned version equals the endorsing peer's version, so the freshness
side condition of `at_most_one` reduces to: the endorsing peers' states are no
newer than the state the validation stream starts from (`s₁ ≼ s`, `s₂ ≼ s`). -/
theorem at_most_one_endorsed {s₁ s₂ : State} {c₁ c₂ : GuardedCall} {t₁ t₂ : Tx}
    {va vb : Version}
    (h₁ : endorse s₁ c₁ = some t₁) (h₂ : endorse s₂ c₂ = some t₂)
    (hid : c₁.id ≠ c₂.id)
    (hg₁ : (c₂.target, vb) ∈ c₁.guards) (hg₂ : (c₁.target, va) ∈ c₂.guards)
    (ts : List Tx) (s : State)
    (hs₁ : ∀ k, s₁ k ≤ s k) (hs₂ : ∀ k, s₂ k ≤ s k) :
    ¬ (t₁ ∈ committed s ts ∧ t₂ ∈ committed s ts) := by
  have hva : va = s₂ c₁.target := (endorse_some_guards_hold h₂ _ hg₂).symm
  have hvb : vb = s₁ c₂.target := (endorse_some_guards_hold h₁ _ hg₁).symm
  exact at_most_one (mutuallyGuarded_of_endorse h₁ h₂ hid hg₁ hg₂) ts s
    (hva ▸ hs₂ c₁.target) (hvb ▸ hs₁ c₂.target)

/-- The same two calls on the unguarded path, endorsed against the same state,
on distinct registries: both commit (B1u, now derived from the call model). -/
theorem b1u_endorsed (s : State) (c₁ c₂ : GuardedCall) (hab : c₁.target ≠ c₂.target) :
    committed s [endorseUnguarded s c₁, endorseUnguarded s c₂]
      = [endorseUnguarded s c₁, endorseUnguarded s c₂] := by
  have hba : c₂.target ≠ c₁.target := fun h => hab h.symm
  simp [committed, readsOk, endorseUnguarded, apply, hba]

/-- Sanity: the B1 fixture of `Example` is produced by `endorse` (the self-guard
is implicit: the target is always read first). -/
example : endorse Example.s₀ ⟨1, Example.a, [(Example.b, 3)]⟩ = some Example.t₁ := by decide
example : endorse Example.s₀ ⟨2, Example.b, [(Example.a, 3)]⟩ = some Example.t₂ := by decide
-- With an explicit self-guard the read set is the same (no duplicate read).
example : endorse Example.s₀ ⟨1, Example.a, [(Example.a, 3), (Example.b, 3)]⟩
    = some Example.t₁ := by decide
/-- FAILED_PRECONDITION: a pin that does not match the peer's state yields no tx. -/
example : endorse Example.s₀ ⟨2, Example.b, [(Example.a, 4)]⟩ = none := by decide

end Argos
